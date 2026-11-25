-- Prove2me | Theorems.Thm_GlobalTheory_DoubledSpace_reducedForm_mk
-- name    : GlobalTheory.DoubledSpace.reducedForm_mk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:25:16.768177+00:00
-- url     : https://prove2.me/theorems/6c576148-f855-4ed4-8b2e-758a7a904903
-- title:
--   Doubled Space: reduced Form mk
-- statement:
--   The Doubled Space construction uses the reduced Form mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L264-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L264-L266

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

theorem GlobalTheory.DoubledSpace.reducedForm_mk (h : W →ₗ[E] W →ₛₗ[σ] E) (hh : ∀ x y, σ (h x y) = h y x)
    (X : Submodule E W) (x y : X.orthogonalBilin h) :
    reducedForm h hh X (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = h x y := by sorry

attribute [defeq] GlobalTheory.DoubledSpace.reducedForm_mk
