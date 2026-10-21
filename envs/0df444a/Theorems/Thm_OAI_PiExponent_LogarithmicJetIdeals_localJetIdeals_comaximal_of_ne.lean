-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeals_comaximal_of_ne
-- name    : OAI.PiExponent.LogarithmicJetIdeals.localJetIdeals_comaximal_of_ne
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T21:09:00.08674+00:00
-- url     : https://prove2.me/theorems/25999025-dfe7-437f-b6ed-182ef0b12d59
-- title:
--   Local jet ideals at distinct centers are comaximal
-- statement:
--   For two center maps differing at any coordinate, their local jet ideals with the same truncation and exponents are comaximal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.localJetIdeals_comaximal_of_ne
    {m : ℕ} (c d : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (h : ∃ i : Fin m, c i ≠ d i) :
    localJetIdeal c T e ⊔ localJetIdeal d T e = ⊤ := by sorry
