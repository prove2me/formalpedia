-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_finite_pair_vectors_iIndepFun
-- name    : Kyprianou.ProofPreparation.finite_pair_vectors_iIndepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:28:46.702193+00:00
-- url     : https://prove2.me/theorems/8618ecb8-8db7-4b14-b9da-4117bbfcd2bf
-- title:
--   Finite-vector preservation of independence
-- statement:
--   Projection from path space onto two arbitrary finite coordinate sets preserves mutual independence and almost-everywhere measurability, using standard measurable evaluation and finite-vector product-space arguments.
-- source:
--   Kyprianou (2006), Chapter 2: independent Lévy–Itô components; Mathlib independence of random variables.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem finite_pair_vectors_iIndepFun
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Fin 3 → Ω → (ℝ≥0 → ℝ))
    (hF : iIndepFun F P)
    (I J : Finset ℝ≥0) :
    iIndepFun
      (fun i ω =>
        ((fun s : I => F i ω s), (fun s : J => F i ω s))) P := by sorry
end Kyprianou.ProofPreparation
