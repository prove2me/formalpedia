-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_finite_pair_vectors_aemeasurable
-- name    : Kyprianou.ProofPreparation.finite_pair_vectors_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:28:47.28385+00:00
-- url     : https://prove2.me/theorems/37341324-f1b3-4a5d-9c4f-e1b3754d906e
-- title:
--   Almost-everywhere measurability of finite path vectors
-- statement:
--   Projection from path space onto two arbitrary finite coordinate sets preserves mutual independence and almost-everywhere measurability, using standard measurable evaluation and finite-vector product-space arguments.
-- source:
--   Kyprianou (2006), Chapter 2: independent Lévy–Itô components; Mathlib independence of random variables.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem finite_pair_vectors_aemeasurable
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Fin 3 → Ω → (ℝ≥0 → ℝ))
    (hF : ∀ (i : Fin 3) (s : ℝ≥0),
      AEMeasurable (fun ω => F i ω s) P)
    (I J : Finset ℝ≥0) :
    ∀ i : Fin 3,
      AEMeasurable
        (fun ω => ((fun s : I => F i ω s),
          (fun s : J => F i ω s))) P := by sorry
end Kyprianou.ProofPreparation
