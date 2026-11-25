-- Prove2me | Theorems.Thm_GlobalTheory_DoubledSpace_glue_isotropic
-- name    : GlobalTheory.DoubledSpace.glue_isotropic
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:25:20.833517+00:00
-- url     : https://prove2.me/theorems/6ea87382-f7e9-49bd-9849-fb95ca0894d0
-- title:
--   Doubled Space: glue isotropic
-- statement:
--   The Doubled Space construction uses the glue isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L344-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L344-L353

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

theorem GlobalTheory.DoubledSpace.glue_isotropic (hh : ∀ x y, σ (h x y) = h y x) {φ : Reduced h X →ₗ[E] Reduced h X'}
    (hφ : ∀ a b, reducedForm h hh X' (φ a) (φ b) = reducedForm h hh X a b) :
    ∀ p ∈ glue h X X' φ, ∀ q ∈ glue h X X' φ, form h p q = 0 := by sorry
