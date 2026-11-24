-- Prove2me | Theorems.Thm_GlobalTheory_NormMod_span_sub_bar
-- name    : GlobalTheory.NormMod.span_sub_bar
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:36:27.498928+00:00
-- url     : https://prove2.me/theorems/9a62eaec-3170-4de9-bb9f-4cf357b7f1ad
-- title:
--   Norm Mod: span sub bar
-- statement:
--   The Norm Mod construction uses the span sub bar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsHostNormModCoprimeLevelHalf.lean#L163-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsHostNormModCoprimeLevelHalf.lean#L163-L192

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormMod
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HostModel
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem GlobalTheory.NormMod.span_sub_bar : Ideal.span (Set.range fun b : 𝓞 E => b - H.bar b) = ⊤ := by sorry
