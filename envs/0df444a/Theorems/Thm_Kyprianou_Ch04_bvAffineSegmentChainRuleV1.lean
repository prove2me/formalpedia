-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvAffineSegmentChainRuleV1
-- name    : Kyprianou.Ch04.bvAffineSegmentChainRuleV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:04:28.315645+00:00
-- url     : https://prove2.me/theorems/7fe2fc91-4f96-4166-a5a3-408aad0e133a
-- title:
--   Fundamental theorem of calculus on a positive-time affine segment
-- statement:
--   Apply the real interval fundamental theorem of calculus on the interior. The chain derivative is the Frechet derivative applied to the affine tangent vector (1,d). The affine derivative integrability lemma supplies the remaining hypothesis.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic finite-jump telescoping.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvAffineSegmentChainRuleV1
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (a d l r : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) :
    f (r, a + d * r) - f (l, a + d * l) =
      ∫ u in l..r, fderiv ℝ f (u, a + d * u) (1, d) := by
  sorry
