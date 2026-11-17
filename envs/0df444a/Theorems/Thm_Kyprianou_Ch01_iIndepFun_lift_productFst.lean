-- Prove2me | Theorems.Thm_Kyprianou_Ch01_iIndepFun_lift_productFst
-- name    : Kyprianou.Ch01.iIndepFun_lift_productFst
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:53:20.510827+00:00
-- url     : https://prove2.me/theorems/b9e068a1-8368-457e-96e9-d54aea56f591
-- title:
--   Finite-grid independence transfers to an independent product probability space
-- statement:
--   For probability laws P and Q on arbitrary measurable spaces, any finite family of measurable real random variables F_i which is independent under P remains independent when lifted to the first-coordinate functions F_i(ω₁) under the product law P ⊗ Q. The argument uses the exact joint distribution characterisation of independence and preservation of the first-coordinate marginal. This is a structural source-exact bridge needed to lift the pure-jump and Gaussian Lévy processes to a common independent product space for Kyprianou Chapter 1 Theorem 1.6.
-- source:
--   Pinned Mathlib ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map, MeasureTheory.measurePreserving_fst and MeasureTheory.Measure.map_map; Kyprianou Chapter 1 Theorem 1.6.

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.iIndepFun_lift_productFst
    {Ω Λ ι : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [Fintype ι]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : ι → Ω → ℝ)
    (hF : ∀ i, Measurable (F i))
    (hIndep : iIndepFun F P) :
    iIndepFun (fun i (p : Ω × Λ) => F i p.1) (P.prod Q) := by
  sorry
