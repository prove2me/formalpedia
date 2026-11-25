-- Prove2me | Theorems.Thm_GlobalTheory_DoubledSpace_finrank_reduced
-- name    : GlobalTheory.DoubledSpace.finrank_reduced
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:25:00.317282+00:00
-- url     : https://prove2.me/theorems/6456d274-ecc7-5e3b-bf5f-0a7535c00a2c
-- title:
--   Doubled Space: finrank reduced
-- statement:
--   The Doubled Space construction uses the finrank reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L360-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L360-L367

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
variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0)
include hσ hh hn

theorem GlobalTheory.DoubledSpace.finrank_reduced (hX : ∀ x ∈ X, ∀ x' ∈ X, h x x' = 0) :
    finrank E (Reduced h X) + 2 * finrank E X = finrank E W := by sorry
