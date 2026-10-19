-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_succ_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_succ_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:37:19.900255+00:00
-- url     : https://prove2.me/theorems/7968dcc9-e4a3-4033-a9f7-9d77cc0d2f91
-- title:
--   Lifted univariate series have no successor-coordinate support
-- statement:
--   A lifted univariate series has zero coefficient at every exponent that is nonzero in any successor coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_succ_support
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (i : Fin m)
    (d : Fin (m + 1) →₀ ℕ) (j : Fin m) (h : d j.succ ≠ 0) :
    MvPowerSeries.coeff d (liftLogSeries m (delta i)) = 0 := by sorry
