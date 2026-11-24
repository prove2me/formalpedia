-- Prove2me | Theorems.Thm_GlobalTheory_SW_mem_stdL
-- name    : GlobalTheory.SW.mem_stdL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:47.547183+00:00
-- url     : https://prove2.me/theorems/7b289a51-7ba9-4edd-b470-36b0dc7af1d8
-- title:
--   SW: mem std L
-- statement:
--   The SW construction uses the mem std L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/AdmissibleIndicatorFunctions.lean#L16-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/AdmissibleIndicatorFunctions.lean#L16-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleIndicatorFunctions
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}

theorem GlobalTheory.SW.mem_stdL {x : Fin n → E} : x ∈ stdL E n ↔ ∀ a, IsIntegral ℤ (x a) := by sorry
