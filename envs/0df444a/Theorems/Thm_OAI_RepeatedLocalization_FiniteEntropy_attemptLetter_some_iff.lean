-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_attemptLetter_some_iff
-- name    : OAI.RepeatedLocalization.FiniteEntropy.attemptLetter_some_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:42:32.378682+00:00
-- url     : https://prove2.me/theorems/e20f9305-8014-4e5f-9a74-59f2fb1f4483
-- title:
--   The attempt letter records exactly the first heavy cell containing the point
-- statement:
--   Fix a dimension $n\ge1$. A dyadic cell is a pair $c=(J,k)$ of a level $\ell(c)=J\in\mathbb{N}$ and an index vector $k\in\{0,1,\dots,2^J-1\}^n$. Its box is $B_c=\prod_{i=1}^{n}\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_i}{\sqrt n\,2^J},\ -\tfrac{1}{2\sqrt n}+\tfrac{k_i+1}{\sqrt n\,2^J}\big)\subseteq\mathbb{R}^n$, a dyadic subcube of $\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$. For cells $c,R$ write $c\preceq R$ ($R$ is a descendant of $c$) if $\ell(c)\le\ell(R)$ and $B_R\subseteq B_c$. Let $P$ be a measure on $\mathbb{R}^n$ (no finiteness is assumed) and let $Q$ be a cell. A cell $R$ is heavy for $(P,Q)$ if $Q\preceq R$, $\ell(Q)<\ell(R)$ and $P(B_R)>2^{-n(\ell(R)-\ell(Q))/2}$. It is first heavy if moreover every heavy cell $E$ with $E\preceq R$ equals $R$. The attempt letter $a(z)$ of a point $z\in\mathbb{R}^n$ is defined with a choice function: if the box of some first heavy cell contains $z$, then $a(z)$ is such a cell, chosen arbitrarily; otherwise $a(z)=\bot$ (none).
--
--   Then for every cell $R$ and every point $z\in\mathbb{R}^n$,
--
--   $$
--   a(z)=R\iff R\ \text{is first heavy for }(P,Q)\ \text{ and }\ z\in B_R .
--   $$
--
--   In particular the arbitrary choice in the definition does not matter: a point lies in the box of at most one first heavy cell. The equivalence identifies the set $\{z: a(z)=R\}$ with $B_R$ or with $\varnothing$. This is the basis for the measurability of the attempt letter and for describing which points of a cell produce the same log.
--
--   **Formalization Note** The left-hand side is `attemptLetter P Q z = some R`, where `attemptLetter` is defined through `Exists.choose`. Masses in the heaviness test are compared through `toReal`, so a cell of infinite $P$-mass is never heavy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/History.lean#L30-L43

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.attemptLetter_some_iff {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q R : Cell n)
    (z : Coordinate n) : attemptLetter P Q z = some R ↔ FirstHeavy P Q R ∧ z ∈ cellSet R := by sorry
