-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalStepGridIdentityV1
-- name    : Kyprianou.Ch04.physicalStepGridIdentityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:43:52.14056+00:00
-- url     : https://prove2.me/theorems/b4563acf-ac8a-5699-8dc6-589c7ef57a79
-- title:
--   physicalStepGridIdentityV1
-- statement:
--   Physical clipped grid step identity or contraction.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact physical compensated integral identity for the finite step weights. -/

theorem Kyprianou.Ch04.physicalStepGridIdentityV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (hmark : ∀ z ∈ B, |z| ≤ 1)
    (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ) (H : ℕ → Ω → ℝ)
    (Y : NNReal → Ω → ℝ)
    (hY : ∀ t w, Y t w =
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(N.N w)) -
        (t : ℝ) * (∫ x in B,x ∂ν)) :
    let g := fun (p : (NNReal × Ω) × ℝ) =>
      B.indicator (fun x => x * ∑ k ∈ Finset.range n,
        (Ioc (u k) (u (k+1))).indicator (fun _ => H k p.1.2) p.1.1) p.2
    ∀ᵐ w ∂P, ∀ t : NNReal,
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
        g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
        g ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν) =
      ∑ k ∈ Finset.range n, H k w *
        (Y (min t (u (k+1))) w-Y (min t (u k)) w) := by
  sorry
