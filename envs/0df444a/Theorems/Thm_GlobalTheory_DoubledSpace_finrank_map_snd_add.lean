-- Prove2me | Theorems.Thm_GlobalTheory_DoubledSpace_finrank_map_snd_add
-- name    : GlobalTheory.DoubledSpace.finrank_map_snd_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:24:56.613008+00:00
-- url     : https://prove2.me/theorems/f70e6c2c-c259-4d36-9648-f1bea6d2f76a
-- title:
--   Doubled Space: finrank map snd add
-- statement:
--   The Doubled Space construction uses the finrank map snd add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L78-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L78-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
open GlobalTheory.DoubledSpace
variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {σ : E →+* E}

theorem GlobalTheory.DoubledSpace.finrank_map_snd_add [FiniteDimensional E W] (I : Submodule E (W × W)) :
    finrank E (I.map (LinearMap.snd E W W)) + finrank E (left I) = finrank E I := by sorry
