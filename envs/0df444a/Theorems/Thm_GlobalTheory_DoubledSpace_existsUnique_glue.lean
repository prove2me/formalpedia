-- Prove2me | Theorems.Thm_GlobalTheory_DoubledSpace_existsUnique_glue
-- name    : GlobalTheory.DoubledSpace.existsUnique_glue
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:25:08.64258+00:00
-- url     : https://prove2.me/theorems/8429e4a8-e31f-5956-ba65-588ad73c9209
-- title:
--   Doubled Space: exists Unique glue
-- statement:
--   The Doubled Space construction uses the exists Unique glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L379-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L379-L429

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

theorem GlobalTheory.DoubledSpace.existsUnique_glue {I : Submodule E (W × W)} (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0)
    (hd : finrank E I = finrank E W) :
    ∃! φ : Reduced h (left I) ≃ₗ[E] Reduced h (right I),
      (∀ a b, reducedForm h hh (right I) (φ a) (φ b) = reducedForm h hh (left I) a b) ∧
        I = glue h (left I) (right I) φ := by sorry
