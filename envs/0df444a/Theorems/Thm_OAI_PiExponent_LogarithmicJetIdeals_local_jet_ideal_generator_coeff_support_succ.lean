-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_generator_coeff_support_succ
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_support_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T11:44:48.616598+00:00
-- url     : https://prove2.me/theorems/1302a762-a3e6-4954-9c0c-d6863ad7d7ff
-- title:
--   Successor jet generator coefficient support
-- statement:
--   If a coefficient of the formal image of a successor jet generator is nonzero, its exponent vector is either the unit exponent at that successor coordinate, or is supported only at coordinate zero with exponent at least the truncation cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_support_succ
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (i : Fin m) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (AdmissibleFormalInterpolation.formalJet c
        (jetCoordinate c T i.succ)) ≠ 0 →
      (∀ j : Fin (m + 1), b j = if j = i.succ then 1 else 0) ∨
        (T i ≤ b 0 ∧ ∀ j : Fin m, b j.succ = 0) := by sorry
