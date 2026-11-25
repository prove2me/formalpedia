-- Prove2me | Theorems.Thm_GlobalTheory_SW_SwdHeat_isSB_member
-- name    : GlobalTheory.SW.SwdHeat.isSB_member
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:11:02.717083+00:00
-- url     : https://prove2.me/theorems/fcdea89f-ec94-52cb-85ef-bbf8ce49687f
-- title:
--   Swd Heat: is SB member
-- statement:
--   The Swd Heat construction uses the is SB member property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatSwd.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatSwd.lean#L43-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThHStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatSwd
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SwdHeat
open GlobalTheory.SW.EisHeat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}

theorem GlobalTheory.SW.SwdHeat.isSB_member {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) : IsSB (φ Λ) := by sorry
