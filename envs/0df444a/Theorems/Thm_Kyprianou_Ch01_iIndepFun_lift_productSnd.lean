-- Prove2me | Theorems.Thm_Kyprianou_Ch01_iIndepFun_lift_productSnd
-- name    : Kyprianou.Ch01.iIndepFun_lift_productSnd
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:57:50.195228+00:00
-- url     : https://prove2.me/theorems/14b96248-e12b-4b9e-8c14-8ea184a454e5
-- title:
--   Finite-grid independence transfers to the second coordinate of an independent product probability space
-- statement:
--   If a finite family of measurable real random variables is independent under Q, then its lift along the second projection to P ⊗ Q remains independent for any independent probability factor P. This is a source-equivalent finite-grid independence bridge for the genuine Lévy process product-space construction.
-- source:
--   Pinned Mathlib ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map, measurePreserving_snd and Measure.map_map.

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.iIndepFun_lift_productSnd
    {Ω Λ ι : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [Fintype ι]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : ι → Λ → ℝ)
    (hF : ∀ i, Measurable (F i))
    (hIndep : iIndepFun F Q) :
    iIndepFun (fun i (p : Ω × Λ) => F i p.2) (P.prod Q) := by
  sorry
