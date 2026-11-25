-- Prove2me | Theorems.Thm_GlobalTheory_DoubledSpace_finrank_add_finrank_orthogonal
-- name    : GlobalTheory.DoubledSpace.finrank_add_finrank_orthogonal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:25:13.509664+00:00
-- url     : https://prove2.me/theorems/452d59cb-df1a-4469-8ccd-4eb65d03586b
-- title:
--   Doubled Space: finrank add finrank orthogonal
-- statement:
--   The Doubled Space construction uses the finrank add finrank orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L14-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L14-L40

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

theorem GlobalTheory.DoubledSpace.finrank_add_finrank_orthogonal [FiniteDimensional E W] {h : W →ₗ[E] W →ₛₗ[σ] E}
    (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
    (hn : ∀ x, (∀ y, h x y = 0) → x = 0) (S : Submodule E W) :
    finrank E S + finrank E (S.orthogonalBilin h) = finrank E W := by sorry
