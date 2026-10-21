-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_simultaneous_power_of_local_powers
-- name    : OAI.PiExponent.LogarithmicJetIdeals.simultaneous_power_of_local_powers
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T21:01:31.924059+00:00
-- url     : https://prove2.me/theorems/25ce0fcc-c227-487c-8cec-1a10cc7692e1
-- title:
--   Local jet ideal powers combine into a simultaneous power
-- statement:
--   If a polynomial lies in the nth power of each local jet ideal at the listed centers, then it lies in the nth power of their simultaneous ideal, provided the center map is injective. Distinct centers make the local ideals comaximal, allowing finite intersection and product to agree.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.simultaneous_power_of_local_powers
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i))
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hlocal : ∀ j : Fin K,
      P ∈ localJetIdeal (fun i => (j.val : ℂ) * r i) T e ^ n) :
    P ∈ (simultaneousJetIdeal K r T e) ^ n := by sorry
