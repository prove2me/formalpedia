-- Prove2me | Theorems.Thm_GlobalTheory_DoubledSpace_mem_glue
-- name    : GlobalTheory.DoubledSpace.mem_glue
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:24:28.342493+00:00
-- url     : https://prove2.me/theorems/ce8bd828-779a-5e34-9561-60d820d5931a
-- title:
--   Doubled Space: mem glue
-- statement:
--   The Doubled Space construction uses the mem glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L273-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L273-L282

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

theorem GlobalTheory.DoubledSpace.mem_glue {h : W →ₗ[E] W →ₛₗ[σ] E} {X X' : Submodule E W}
    {φ : Reduced h X →ₗ[E] Reduced h X'} {x y : W} :
    (x, y) ∈ glue h X X' φ ↔ ∃ (hx : x ∈ X.orthogonalBilin h) (hy : y ∈ X'.orthogonalBilin h),
      φ (Submodule.Quotient.mk ⟨x, hx⟩) = Submodule.Quotient.mk ⟨y, hy⟩ := by sorry
