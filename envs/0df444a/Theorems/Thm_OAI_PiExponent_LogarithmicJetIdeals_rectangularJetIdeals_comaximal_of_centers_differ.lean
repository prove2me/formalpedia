-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_rectangularJetIdeals_comaximal_of_centers_differ
-- name    : OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeals_comaximal_of_centers_differ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:04:16.970626+00:00
-- url     : https://prove2.me/theorems/e2c2267b-5b11-4002-924e-b46cc19b0e8f
-- title:
--   Distinct rectangular jet ideals are comaximal
-- statement:
--   If two centers differ in at least one coordinate, their rectangular jet ideals are comaximal, for every degree vector.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_RectangularJetIdeal
import Mathlib.RingTheory.Ideal.Operations

theorem OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeals_comaximal_of_centers_differ
    {m : Nat} (c d : Fin m -> Complex) (degree : Fin (m + 1) -> Nat)
    (hd : Exists fun k => Not (c k = d k)) :
    OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal c degree ⊔
      OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal d degree = ⊤ := by sorry
