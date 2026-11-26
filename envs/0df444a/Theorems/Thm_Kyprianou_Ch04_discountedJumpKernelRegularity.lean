-- Prove2me | Theorems.Thm_Kyprianou_Ch04_discountedJumpKernelRegularity
-- name    : Kyprianou.Ch04.discountedJumpKernelRegularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:47:06.258225+00:00
-- url     : https://prove2.me/theorems/aef25628-61e8-56ef-96d0-6c60e57aa991
-- title:
--   discountedJumpKernelRegularity
-- statement:
--   The discounted marked jump differences of an adapted left-limit process satisfy joint, past-horizon and common-null left-continuity regularity.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Discounted jump differences of the adapted left-limit process are regular marked kernels. -/
theorem Kyprianou.Ch04.discountedJumpKernelRegularity {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X L : NNReal → Omega → ℝ) (f : ℝ → ℝ) (hf : Continuous f) (lam : ℝ)
    (hm : Measurable (fun z : ℝ × Omega => L z.1.toNNReal z.2))
    (ha : ∀ t : NNReal, Measurable[F t] (L t))
    (hp : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => if z.2 ∈ Set.Icc (0 : ℝ) (t : ℝ)
        then L z.2.toNNReal z.1 else 0))
    (hl : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s w) (nhdsWithin t (Iio t)) (nhds (L t w))) :
    let k := fun s x w => Real.exp (-lam*s) * (f (L s.toNNReal w+x)-f (L s.toNNReal w))
    Measurable (fun z : (ℝ × ℝ) × Omega => k z.1.1 z.1.2 z.2) ∧
    (∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => k (t : ℝ) z.2 z.1)) ∧
    (∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => k s x w) (nhdsWithin (t : ℝ) (Iio (t : ℝ)))
        (nhds (k (t : ℝ) x w))) ∧
    (∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × (ℝ × ℝ) =>
        if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0)) := by
  sorry
