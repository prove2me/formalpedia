-- Prove2me | Theorems.Thm_GlobalTheory_doubled_isotropic_structure_general
-- name    : GlobalTheory.doubled_isotropic_structure_general
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:24:52.876111+00:00
-- url     : https://prove2.me/theorems/6bf04709-6464-59e3-957a-1e40ceb43849
-- title:
--   Global Theory: doubled isotropic structure general
-- statement:
--   The Global Theory construction uses the doubled isotropic structure general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L437-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L437-L474

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
open DoubledSpace

theorem GlobalTheory.doubled_isotropic_structure_general {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {σ : E →+* E} (hσ : Function.Involutive σ)
    {h : W →ₗ[E] W →ₛₗ[σ] E} (hh : ∀ x y, σ (h x y) = h y x)
    (hn : ∀ x, (∀ y, h x y = 0) → x = 0) :
    (∀ I : Submodule E (W × W), (∀ p ∈ I, ∀ q ∈ I, h p.1 q.1 - h p.2 q.2 = 0) →
      finrank E I = finrank E W →
      (∀ x ∈ left I, ∀ x' ∈ left I, h x x' = 0) ∧
      (∀ y ∈ right I, ∀ y' ∈ right I, h y y' = 0) ∧
      finrank E (left I) = finrank E (right I) ∧
      I.map (LinearMap.fst E W W) = (left I).orthogonalBilin h ∧
      I.map (LinearMap.snd E W W) = (right I).orthogonalBilin h ∧
      (left I = ⊥ ↔ ∃! γ : W ≃ₗ[E] W,
        (∀ x y, h (γ x) (γ y) = h x y) ∧ I = (γ : W →ₗ[E] W).graph) ∧
      (∀ u : W →ₗ[E] W, Function.Injective u →
        (∀ x ∈ (left I).orthogonalBilin h, u x - x ∈ left I) →
        I.map (u.prodMap LinearMap.id) = I) ∧
      (∀ u : W →ₗ[E] W, Function.Injective u →
        (∀ y ∈ (right I).orthogonalBilin h, u y - y ∈ right I) →
        I.map (LinearMap.id.prodMap u) = I) ∧
      (∀ ξ ∈ left I, ∀ (b : E) (u : W →ₗ[E] W), (∀ v, u v = v + (b * h v ξ) • ξ) →
        I.map (u.prodMap LinearMap.id) = I) ∧
      (∃! φ : Reduced h (left I) ≃ₗ[E] Reduced h (right I),
        (∀ a b, reducedForm h hh (right I) (φ a) (φ b) = reducedForm h hh (left I) a b) ∧
          I = glue h (left I) (right I) φ)) ∧
    (∀ X X' : Submodule E W, (∀ x ∈ X, ∀ x' ∈ X, h x x' = 0) → (∀ y ∈ X', ∀ y' ∈ X', h y y' = 0) →
      ∀ φ : Reduced h X ≃ₗ[E] Reduced h X',
        (∀ a b, reducedForm h hh X' (φ a) (φ b) = reducedForm h hh X a b) →
        (∀ p ∈ glue h X X' φ, ∀ q ∈ glue h X X' φ, h p.1 q.1 - h p.2 q.2 = 0) ∧
        finrank E (glue h X X' φ) = finrank E W ∧
        left (glue h X X' φ) = X ∧ right (glue h X X' φ) = X') := by sorry
