-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_measurable_attemptLetter
-- name    : OAI.RepeatedLocalization.FiniteEntropy.measurable_attemptLetter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:43:26.210299+00:00
-- url     : https://prove2.me/theorems/b6114e96-a164-47be-ab53-a4dee122ec20
-- title:
--   Measurability of the attempt-letter map
-- statement:
--   Fix a dimension $n\ge1$. A dyadic cell is a pair $c=(J,k)$ of a level $\ell(c)=J\in\mathbb{N}$ and an index vector $k\in\{0,1,\dots,2^J-1\}^n$. Its box is $B_c=\prod_{i=1}^{n}\big[-\tfrac{1}{2\sqrt n}+\tfrac{k_i}{\sqrt n\,2^J},\ -\tfrac{1}{2\sqrt n}+\tfrac{k_i+1}{\sqrt n\,2^J}\big)\subseteq\mathbb{R}^n$, a dyadic subcube of $\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$. For cells $c,R$ write $c\preceq R$ ($R$ is a descendant of $c$) if $\ell(c)\le\ell(R)$ and $B_R\subseteq B_c$. Let $P$ be a measure on $\mathbb{R}^n$ and $Q$ a cell. A cell $R$ is heavy for $(P,Q)$ if $Q\preceq R$, $\ell(Q)<\ell(R)$ and $P(B_R)>2^{-n(\ell(R)-\ell(Q))/2}$. It is first heavy if moreover every heavy cell $E$ with $E\preceq R$ equals $R$. Let $\mathcal{L}_n=\{\bot\}\cup\{\text{cells}\}$ be the set of letters. The attempt letter $a(z)\in\mathcal{L}_n$ of $z\in\mathbb{R}^n$ is a first heavy cell whose box contains $z$, picked by a fixed choice function, if there is one, and $\bot$ otherwise.
--
--   Equip $\mathbb{R}^n$ with its Borel $\sigma$-algebra and the countable set $\mathcal{L}_n$ with the discrete $\sigma$-algebra. Then the attempt-letter map
--
--   $$
--   a:\mathbb{R}^n\to\mathcal{L}_n,\qquad z\mapsto a(z),
--   $$
--
--   is measurable; equivalently, $\{z\in\mathbb{R}^n:\ a(z)=b\}$ is a Borel set for every letter $b$.
--
--   The attempt letter is the elementary step of the repeated-localization procedure. Its measurability, applied to the conditioned measures that occur along the way, passes to the run after $N$ steps, the number of attempts and the terminal log, so that these are random variables under $P$.
--
--   **Formalization Note** The statement is `Measurable (attemptLetter P Q)` for an arbitrary measure `P`. The $\sigma$-algebra on coordinates is the product one, which is the Borel $\sigma$-algebra, and letters carry the instance `letterMeasurableSpace`, the top $\sigma$-algebra.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/History.lean#L49-L73

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.measurable_attemptLetter {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (attemptLetter P Q) := by sorry
