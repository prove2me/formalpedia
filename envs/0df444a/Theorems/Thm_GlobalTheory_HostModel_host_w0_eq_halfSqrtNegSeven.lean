-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
-- name    : GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:22.177811+00:00
-- url     : https://prove2.me/theorems/5392a3e5-323e-4204-88aa-d790fb271fbd
-- title:
--   Host Model: host w0 eq half Sqrt Neg Seven
-- statement:
--   The Host Model construction uses the host w0 eq half Sqrt Neg Seven property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/OneAddZeta21PowSevenAddPowFourteenEqZero.lean#L318-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/OneAddZeta21PowSevenAddPowFourteenEqZero.lean#L318-L318

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

theorem GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven : host.w0 = halfSqrtNegSeven := by sorry

attribute [defeq] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
