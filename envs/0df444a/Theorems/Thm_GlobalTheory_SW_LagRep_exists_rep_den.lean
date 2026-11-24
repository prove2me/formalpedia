-- Prove2me | Theorems.Thm_GlobalTheory_SW_LagRep_exists_rep_den
-- name    : GlobalTheory.SW.LagRep.exists_rep_den
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:38.397278+00:00
-- url     : https://prove2.me/theorems/6c68cc09-c525-4525-9e61-1dd5d00635b5
-- title:
--   Lag Rep: exists rep den
-- statement:
--   The Lag Rep construction uses the exists rep den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LinearIndependentMul.lean#L74-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LinearIndependentMul.lean#L74-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LagRep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.LagRep.exists_rep_den : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ),
    ∃ c : ℕ, 0 < c ∧ ∀ U : Lag E N, ∃ γ ∈ UU E N, Den c γ ∧ botSpan γ = U.1 := by sorry
