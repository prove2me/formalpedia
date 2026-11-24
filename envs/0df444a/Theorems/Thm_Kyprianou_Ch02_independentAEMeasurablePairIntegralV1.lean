-- Prove2me | Theorems.Thm_Kyprianou_Ch02_independentAEMeasurablePairIntegralV1
-- name    : Kyprianou.Ch02.independentAEMeasurablePairIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:54:00.123003+00:00
-- url     : https://prove2.me/theorems/036b9930-058d-435e-a003-6887b1b69218
-- title:
--   Independent almost-everywhere measurable pair integral disintegration
-- statement:
--   The joint pushforward of independent variables is the product of their marginal laws. Boundedness ensures integrability, and Fubini and change of variables establish the result for almost-everywhere measurable maps.
-- source:
--   Product measure and independence; Kyprianou (2006), Chapter 2, Lemma 2.15.

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch02.independentAEMeasurablePairIntegralV1
    {Ω A B : Type} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : Ω → A) (b : Ω → B) (ha : AEMeasurable a P) (hb : AEMeasurable b P)
    (hind : IndepFun a b P)
    (F : A × B → ℂ) (hF : Measurable F) (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) :
    (∫ ω, F (a ω, b ω) ∂P) = ∫ ω, (∫ ω', F (a ω, b ω') ∂P) ∂P := by sorry
