-- Prove2me | Theorems.Thm_GlobalTheory_DoubledSpace_left_eq_bot_iff
-- name    : GlobalTheory.DoubledSpace.left_eq_bot_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:24:32.729216+00:00
-- url     : https://prove2.me/theorems/8f62ce85-c283-546c-b78b-e08844ce8418
-- title:
--   Doubled Space: left eq bot iff
-- statement:
--   The Doubled Space construction uses the left eq bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L147-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L147-L197

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
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {I : Submodule E (W × W)}
variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0) (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0)
  (hd : finrank E I = finrank E W)
include hσ hh hn hI hd

theorem GlobalTheory.DoubledSpace.left_eq_bot_iff :
    left I = ⊥ ↔ ∃! γ : W ≃ₗ[E] W,
      (∀ x y, h (γ x) (γ y) = h x y) ∧ I = (γ : W →ₗ[E] W).graph := by sorry
