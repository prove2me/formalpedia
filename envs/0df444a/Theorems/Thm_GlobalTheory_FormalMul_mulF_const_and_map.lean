-- Prove2me | Theorems.Thm_GlobalTheory_FormalMul_mulF_const_and_map
-- name    : GlobalTheory.FormalMul.mulF_const_and_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:49.299419+00:00
-- url     : https://prove2.me/theorems/ae7b62e1-8f2f-4e8a-978a-0061c3512408
-- title:
--   Formal Mul: mul F const and map
-- statement:
--   The Formal Mul construction uses the mul F const and map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MulFConstAndMap.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MulFConstAndMap.lean#L36-L39

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

theorem GlobalTheory.FormalMul.mulF_const_and_map : ∀ (T O : Type) [CommRing T] [CommRing O] (io : T →+* O) (d : ℕ) (F : FGLaw T d)
    (N : ℕ) (j : Fin d), MvPowerSeries.constantCoeff (mulF F.F N j) = 0 ∧
      mulF (F.mapF io) N j = MvPowerSeries.map io (mulF F.F N j) := by sorry
