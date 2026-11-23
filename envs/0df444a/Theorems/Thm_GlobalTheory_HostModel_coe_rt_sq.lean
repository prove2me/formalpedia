-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_coe_rt_sq
-- name    : GlobalTheory.HostModel.coe_rt_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:45.190933+00:00
-- url     : https://prove2.me/theorems/276d1fe9-f35d-400e-99f0-6fe4dffe12b2
-- title:
--   Host Model: coe rt sq
-- statement:
--   The Host Model construction uses the coe rt sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/IsCoprimeTwoSubRtTwoAddRt.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/IsCoprimeTwoSubRtTwoAddRt.lean#L13-L15

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConjEmbeddingRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.HostModel.coe_rt_sq (H : Host E) : (H.rt : E) ^ 2 = -(H.d : E) := by sorry
