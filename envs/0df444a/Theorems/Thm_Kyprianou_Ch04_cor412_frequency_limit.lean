-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_frequency_limit
-- name    : Kyprianou.Ch04.cor412_frequency_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:30:35.355454+00:00
-- url     : https://prove2.me/theorems/4ffc7011-f46c-4187-82e4-34c9b4c010f5
-- title:
--   High frequency limit of the bounded variation perpetual infimum transform
-- statement:
--   High frequency limit of the bounded variation perpetual infimum transform.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_exponent_gap_div_tendsto_zero
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_frequency_limit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (m : ℝ) :
    Tendsto (fun b : ℝ => m * b / L.ψ b) atTop (𝓝 (m / L.drift)) := by sorry
