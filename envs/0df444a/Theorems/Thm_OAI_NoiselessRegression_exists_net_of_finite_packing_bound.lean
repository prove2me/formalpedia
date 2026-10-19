-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_exists_net_of_finite_packing_bound
-- name    : OAI.NoiselessRegression.exists_net_of_finite_packing_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:34:29.686157+00:00
-- url     : https://prove2.me/theorems/09749616-8ddc-48bf-bffc-9c74fc7a31d7
-- title:
--   Maximal separated sets are nets
-- statement:
--   Let $A$ be a subset of a metric space and $r\ge0$, and suppose every $r$-separated finite subset of $A$ (pairwise distances $>r$) has at most $N$ points. Then there is a finite $r$-separated $s\subseteq A$ that is an $r$-net of $A$:
--   $$
--   \forall x\in A\ \exists y\in s:\ d(x,y)\le r .
--   $$
--
--   It provides the finite nets used in the localization arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Nets.lean#L92-L133

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
universe u
variable {E : Type*} [PseudoMetricSpace E]

theorem OAI.NoiselessRegression.exists_net_of_finite_packing_bound (A : Set E) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hcard : ∀ s : Finset E, (∀ x ∈ s, x ∈ A) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) → s.card ≤ N) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) ∧
      ∀ x ∈ A, ∃ y ∈ s, dist x y ≤ r := by sorry
