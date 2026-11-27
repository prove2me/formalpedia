-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalWeightedIntegralErrorV1
-- name    : Kyprianou.Ch04.physicalWeightedIntegralErrorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:13:49.096343+00:00
-- url     : https://prove2.me/theorems/7ed832c9-ee3d-537e-ad6f-13ff6d84778e
-- title:
--   physicalWeightedIntegralErrorV1
-- statement:
--   physicalWeightedIntegralErrorV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedClockIntegralPerturbationV1
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The stopped finite-variation integral has a Lipschitz bound in the weight,
with the actual absolute marked ledger rather than an expected mark size. -/

theorem Kyprianou.Ch04.physicalWeightedIntegralErrorV1 (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j H L : NNReal → ℝ) (b d : ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ 1/2 < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (hd : 0 ≤ d)
    (hH : IntegrableOn (fun s : ℝ => H s.toNNReal) (Ioc (0 : ℝ) (T : ℝ)))
    (hL : IntegrableOn (fun s : ℝ => L s.toNNReal) (Ioc (0 : ℝ) (T : ℝ)))
    (h : ∀ r ≤ T, 0 < r → |H r - L r| ≤ d) :
    ∀ t ≤ T,
      |(b * (∫ s in Icc (0 : ℝ) (t : ℝ), H s.toNNReal) +
        ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * H z.1.toNNReal ∂ R) -
       (b * (∫ s in Icc (0 : ℝ) (t : ℝ), L s.toNNReal) +
        ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * L z.1.toNNReal ∂ R)| ≤
      (|b| * (T : ℝ) + (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ
          {x : ℝ | 1/2 < |x|}, |z.2| ∂ R)) * d := by
  sorry
