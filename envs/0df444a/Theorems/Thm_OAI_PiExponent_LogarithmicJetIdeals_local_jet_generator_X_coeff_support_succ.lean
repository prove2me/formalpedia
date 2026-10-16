-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_generator_X_coeff_support_succ
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_generator_X_coeff_support_succ
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T20:40:27.647951+00:00
-- url     : https://prove2.me/theorems/dbe5f560-c948-4e37-b8a3-977bb145d3d1
-- title:
--   Successor variable coefficient support
-- statement:
--   A nonzero natural coefficient of the successor variable forces the exponent function to be exactly its unit exponent. Every other exponent, including the constant exponent, has zero coefficient.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_generator_X_coeff_support_succ
    {m : ℕ} (b : Fin (m + 1) → ℕ) (i : Fin m) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (MvPowerSeries.X i.succ) ≠ 0 →
      ∀ j : Fin (m + 1), b j = if j = i.succ then 1 else 0 := by sorry
