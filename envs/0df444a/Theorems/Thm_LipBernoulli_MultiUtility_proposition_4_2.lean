-- Prove2me | Theorems.Thm_LipBernoulli_MultiUtility_proposition_4_2
-- name    : LipBernoulli.MultiUtility.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:30.16788+00:00
-- url     : https://prove2.me/theorems/bb21e578-9bb8-487c-9e0f-bfefc2ec3707
-- title:
--   Proposition 4.2, p. 13 — a preorder with a Lipschitz expected multi-utility is affine and Lipschitz
-- statement:
--   Let $X$ be a separable metric space with its Borel $\sigma$-algebra and let $\mathcal U$ be a family of Lipschitz functions on $X$. Let $\succsim$ be the preorder on $\Delta_1(X)$ defined by
--   $$
--   p \succsim q \iff \int_X u\,\mathrm dp \ge \int_X u\,\mathrm dq \text{ for every } u \in \mathcal U \qquad (p,q\in\Delta_1(X)).
--   $$
--   Then $\succsim$ is affine on $\Delta_1(X)$ and Lipschitz in the sense of Definition 4.1.
--
--   This is the "if" direction of the main theorem (Theorem 4.6).
--
--   **Formalization Note** The relation is any relation on measures that agrees with the displayed one on $\Delta_1(X)$; its values elsewhere are irrelevant. Each $u$ has its own Lipschitz constant, and $\mathcal U$ may be empty.
-- source:
--   Ok & Weaver, Lipschitz Bernoulli Utility Functions, arXiv:2104.11205v1, Proposition 4.2, p. 13

import Mathlib
import Definitions.Def_LipBernoulli_MultiUtility_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace LipBernoulli.MultiUtility

/-- Proposition 4.2, p. 13. Let `X` be a separable metric space and `U` a family of Lipschitz
functions on `X`. The preorder `≿` on `Δ₁(X)` defined by `p ≿ q` iff `∫ u dp ≥ ∫ u dq` for every
`u ∈ U` is affine and Lipschitz. -/
theorem proposition_4_2 {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (U : Set (X → ℝ)) (hU : ∀ u ∈ U, ∃ L : ℝ≥0, LipschitzWith L u)
    (R : Measure X → Measure X → Prop)
    (hR : ∀ p ∈ Delta1 X, ∀ q ∈ Delta1 X, (R p q ↔ ∀ u ∈ U, ∫ x, u x ∂q ≤ ∫ x, u x ∂p)) :
    IsAffine (Delta1 X) R ∧ IsLipschitzPref R := by sorry

end LipBernoulli.MultiUtility
