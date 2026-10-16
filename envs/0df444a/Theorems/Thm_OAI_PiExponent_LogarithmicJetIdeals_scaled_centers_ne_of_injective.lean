-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_scaled_centers_ne_of_injective
-- name    : OAI.PiExponent.LogarithmicJetIdeals.scaled_centers_ne_of_injective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T21:09:22.680989+00:00
-- url     : https://prove2.me/theorems/573fe095-9627-447e-9ba3-8d367c9b062d
-- title:
--   Injective scaled centers differ in a coordinate
-- statement:
--   If the functions of coordinates obtained by scaling r by j.val are injectively indexed, then distinct indices give different values at some coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.scaled_centers_ne_of_injective
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i))
    {j k : Fin K} (hjk : j ≠ k) :
    ∃ i : Fin m, (j.val : ℂ) * r i ≠ (k.val : ℂ) * r i := by sorry
