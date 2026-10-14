-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeal_isCoprime_of_ne
-- name    : OAI.PiExponent.LogarithmicJetIdeals.localJetIdeal_isCoprime_of_ne
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T23:41:38.768493+00:00
-- url     : https://prove2.me/theorems/826547b8-8ee1-4004-8f8a-833a3f846dd3
-- title:
--   Distinct local jet centers give comaximal ideals
-- statement:
--   For any two distinct center functions, the corresponding local jet ideals are comaximal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.localJetIdeal_isCoprime_of_ne
    {m : ℕ} (c d : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (hcd : c ≠ d) :
    IsCoprime (localJetIdeal c T e) (localJetIdeal d T e) := by sorry
