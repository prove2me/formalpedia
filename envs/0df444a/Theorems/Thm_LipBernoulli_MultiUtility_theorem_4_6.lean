-- Prove2me | Theorems.Thm_LipBernoulli_MultiUtility_theorem_4_6
-- name    : LipBernoulli.MultiUtility.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:25.090057+00:00
-- url     : https://prove2.me/theorems/81914888-a737-4651-8b6b-685deb3b8450
-- title:
--   Theorem 4.6, p. 16 — a preorder on Δ1(X) is Lipschitz and affine iff it has a Lipschitz Bernoulli multi-utility
-- statement:
--   Let $X$ be a separable metric space with its Borel $\sigma$-algebra and let $\succsim$ be a preorder on $\Delta_1(X)$, the Borel probability measures on $X$ with finite first moment. Then $\succsim$ is Lipschitz (Definition 4.1) and affine if and only if there is a family $\mathcal U$ of Lipschitz functions on $X$ such that
--   $$
--   p \succsim q \iff \int_X u\,\mathrm dp \ge \int_X u\,\mathrm dq \text{ for every } u\in\mathcal U \qquad (p, q\in\Delta_1(X)). \tag{17}
--   $$
--
--   This is the expected Lipschitz multi-utility theorem, the main result of the paper: preferences over risky prospects that satisfy the independence axiom and the quantitative Lipschitz continuity of Definition 4.1 are exactly those that compare lotteries by the expected values of a family of Lipschitz Bernoulli utility functions.
--
--   **Formalization Note** The preorder is a relation on measures that is reflexive and transitive on $\Delta_1(X)$; affinity, the Lipschitz property and the representation all quantify over $\Delta_1(X)$ only. The family $\mathcal U$ may be empty (as on p. 16; then $\succsim$ is the total relation), and each $u\in\mathcal U$ has its own Lipschitz constant.
-- source:
--   Ok & Weaver, Lipschitz Bernoulli Utility Functions, arXiv:2104.11205v1, Theorem 4.6 and (17), p. 16

import Mathlib
import Definitions.Def_LipBernoulli_MultiUtility_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace LipBernoulli.MultiUtility

/-- Theorem 4.6, p. 16. Let `X` be a separable metric space and `≿` a preorder on `Δ₁(X)`. Then `≿`
is Lipschitz and affine if and only if there is a family `U` of Lipschitz functions on `X` such
that (17) `p ≿ q` iff `∫ u dp ≥ ∫ u dq` for every `u ∈ U` (for all `p, q ∈ Δ₁(X)`). -/
theorem theorem_4_6 {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (R : Measure X → Measure X → Prop) (hR : IsPreorderOn (Delta1 X) R) :
    (IsLipschitzPref R ∧ IsAffine (Delta1 X) R) ↔ ∃ U : Set (X → ℝ), RepresentedBy U R := by sorry

end LipBernoulli.MultiUtility
