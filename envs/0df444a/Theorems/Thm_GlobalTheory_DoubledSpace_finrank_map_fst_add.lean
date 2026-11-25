-- Prove2me | Theorems.Thm_GlobalTheory_DoubledSpace_finrank_map_fst_add
-- name    : GlobalTheory.DoubledSpace.finrank_map_fst_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:24:22.221944+00:00
-- url     : https://prove2.me/theorems/8275deaa-dc78-5f3b-aa21-2eab6f9233a2
-- title:
--   Doubled Space: finrank map fst add
-- statement:
--   The Doubled Space construction uses the finrank map fst add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L60-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L60-L76

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

theorem GlobalTheory.DoubledSpace.finrank_map_fst_add [FiniteDimensional E W] (I : Submodule E (W × W)) :
    finrank E (I.map (LinearMap.fst E W W)) + finrank E (right I) = finrank E I := by sorry
