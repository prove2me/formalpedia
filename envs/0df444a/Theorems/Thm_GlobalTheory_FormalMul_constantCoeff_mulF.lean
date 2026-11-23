-- Prove2me | Theorems.Thm_GlobalTheory_FormalMul_constantCoeff_mulF
-- name    : GlobalTheory.FormalMul.constantCoeff_mulF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:40.236826+00:00
-- url     : https://prove2.me/theorems/196d91fc-c737-453a-8dd0-b9df4e7ae7fa
-- title:
--   Formal Mul: constant Coeff mul F
-- statement:
--   The Formal Mul construction uses the constant Coeff mul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MulFConstAndMap.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MulFConstAndMap.lean#L12-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MulFConstAndMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.FormalMul

theorem GlobalTheory.FormalMul.constantCoeff_mulF {T : Type} [CommRing T] {d : ℕ} (F : Fin d → PS T 2 d)
    (hF : ∀ i, constantCoeff (F i) = 0) (N : ℕ) : ∀ j, constantCoeff (mulF F N j) = 0 := by sorry
