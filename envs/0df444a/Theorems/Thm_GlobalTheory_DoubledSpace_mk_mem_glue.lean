-- Prove2me | Theorems.Thm_GlobalTheory_DoubledSpace_mk_mem_glue
-- name    : GlobalTheory.DoubledSpace.mk_mem_glue
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:30:09.377839+00:00
-- url     : https://prove2.me/theorems/384f0098-745f-54f5-b984-4b7399e02a3c
-- title:
--   Doubled Space: mk mem glue
-- statement:
--   The Doubled Space construction uses the mk mem glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L288-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L288-L292

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
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {X X' : Submodule E W}

theorem GlobalTheory.DoubledSpace.mk_mem_glue {φ : Reduced h X →ₗ[E] Reduced h X'} (x : X.orthogonalBilin h)
    (y : X'.orthogonalBilin h) :
    (x.1, y.1) ∈ glue h X X' φ ↔ φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by sorry
