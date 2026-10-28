-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_span_components_mem_20261024
-- name    : OAI.PiExponent.FormalInterpolation.span_components_mem_20261024
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T15:18:24.281997+00:00
-- url     : https://prove2.me/theorems/8c44aada-db6b-47fa-8cce-e2d45fdc3974
-- title:
--   Weighted components of the generated ideal remain in the ideal
-- statement:
--   Every weighted homogeneous component of an element of the span ideal belongs to that ideal. Each generator is itself the component of a polynomial at degree `q`, hence belongs to the degree-`q` homogeneous submodule. The weighted graded algebra and homogeneous-ideal span theorem then show that the span ideal is homogeneous, which gives component closure. This removes the ideal-homogeneity interface and the instance requirement from the parent. The claim does not need positivity of weights or `q > 0`; degree zero and zero generators are included.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem OAI.PiExponent.FormalInterpolation.span_components_mem_20261024
    {d : Nat} (w : Fin d → Rat) (q : Rat)
    (S : Set (MvPolynomial (Fin d) Complex))
    (hhom : ∀ p ∈ S, ∃ g,
      p = MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : Rat)) q g) :
    ∀ p ∈ Ideal.span S, ∀ r : Rat,
      MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : Rat)) r p ∈ Ideal.span S := by sorry
