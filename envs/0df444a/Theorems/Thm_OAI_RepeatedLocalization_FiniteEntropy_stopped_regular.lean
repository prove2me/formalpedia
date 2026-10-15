-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_stopped_regular
-- name    : OAI.RepeatedLocalization.FiniteEntropy.stopped_regular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:42:12.890672+00:00
-- url     : https://prove2.me/theorems/12b7a8e0-7251-43fa-ac62-7dfc0695eb4e
-- title:
--   Conditioning on a residual of mass at least one half gives a regular law
-- statement:
--   Fix a dimension $n\ge1$. A dyadic cell is a pair $c=(J,k)$ of a level $\ell(c)=J\in\mathbb{N}$ and an index vector $k\in\{0,1,\dots,2^J-1\}^n$. Its box is $B_c=\prod_{i=1}^{n}\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_i}{\sqrt n\,2^J},\ -\tfrac{1}{2\sqrt n}+\tfrac{k_i+1}{\sqrt n\,2^J}\big)\subseteq\mathbb{R}^n$, a dyadic subcube of $\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$. For cells $c,R$ write $c\preceq R$ ($R$ is a descendant of $c$) if $\ell(c)\le\ell(R)$ and $B_R\subseteq B_c$. Let $P$ be a probability measure on $\mathbb{R}^n$, let $Q$ be a cell, and put $\theta(h)=2^{-nh/2}$ for $h\in\mathbb{N}$. A cell $R$ is heavy (for $P$ below $Q$) if $Q\preceq R$, $\ell(Q)<\ell(R)$ and $P(B_R)>\theta(\ell(R)-\ell(Q))$. It is first heavy if moreover every heavy cell $E$ with $E\preceq R$ equals $R$. The residual is
--
--   $$\mathrm{Res}=B_Q\setminus\bigcup\{B_R:\ R\text{ first heavy}\}.$$
--
--   Assume that $P(\mathrm{Res})\ge\tfrac12$, and let $\mu=P(\cdot\mid\mathrm{Res})$ be $P$ conditioned on the residual. Then $\mu$ is regular for $Q$, that is:
--
--   1. $\mu(B_Q)=1$;
--   2. for every cell $R$ with $Q\preceq R$ and $\ell(Q)<\ell(R)$,
--      $$\mu(B_R)\le2\,\theta\big(\ell(R)-\ell(Q)\big)=2\cdot2^{-n(\ell(R)-\ell(Q))/2}.$$
--
--   This is the stopping criterion of the repeated-localization procedure. When the part of the current cell not covered by first heavy cells carries at least half of the mass, the procedure stops, and the law conditioned on that part gives every proper dyadic descendant at most twice its threshold mass. Regularity of the terminal law is one of the guarantees of the finite-entropy regularization theorem.
--
--   **Formalization Note** The conclusion is `Regular (ProbabilityTheory.cond P (residual P Q)) Q`. The hypothesis and the masses in `Heavy` and `Regular` are real numbers obtained with `toReal`, and $\theta$ is `threshold n h`, a real power of $2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/FirstHeavy.lean#L138-L168

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.stopped_regular {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hq : (1/2:ℝ) ≤ (P (residual P Q)).toReal) :
    Regular (ProbabilityTheory.cond P (residual P Q)) Q := by sorry
