-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_host_d
-- name    : GlobalTheory.HostModel.host_d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:05.614919+00:00
-- url     : https://prove2.me/theorems/46126f6a-e7eb-4032-bb11-76bfad59679b
-- title:
--   Host Model: host d
-- statement:
--   The Host Model construction uses the host d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/OneAddZeta21PowSevenAddPowFourteenEqZero.lean#L314-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/OneAddZeta21PowSevenAddPowFourteenEqZero.lean#L314-L314

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.HostModel.host_d : host.d = 7 := by sorry

attribute [defeq] GlobalTheory.HostModel.host_d
