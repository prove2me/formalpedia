-- Prove2me | Theorems.Thm_GlobalTheory_doubled_isotropic_structure
-- name    : GlobalTheory.doubled_isotropic_structure
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:25:05.699248+00:00
-- url     : https://prove2.me/theorems/bfbf8e97-27e0-46a7-8904-b5383d6876a9
-- title:
--   Global Theory: doubled isotropic structure
-- statement:
--   The Global Theory construction uses the doubled isotropic structure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L496-L560
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean#L496-L560

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
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix LocalLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem GlobalTheory.doubled_isotropic_structure (G : Matrix (Fin N) (Fin N) E)
    (hG : ∀ a b, cc (G a b) = G b a) (hdet : G.det ≠ 0) :
    (∀ I : Submodule E ((Fin N → E) × (Fin N → E)),
      (∀ p ∈ I, ∀ q ∈ I, herm G p.1 q.1 - herm G p.2 q.2 = 0) → finrank E I = N →
      (∀ x ∈ left I, ∀ x' ∈ left I, herm G x x' = 0) ∧
      (∀ y ∈ right I, ∀ y' ∈ right I, herm G y y' = 0) ∧
      finrank E (left I) = finrank E (right I) ∧
      I.map (LinearMap.fst E _ _) = (left I).orthogonalBilin (hermPairing G) ∧
      I.map (LinearMap.snd E _ _) = (right I).orthogonalBilin (hermPairing G) ∧
      (left I = ⊥ ↔ ∃! γ : (Fin N → E) ≃ₗ[E] (Fin N → E),
        (∀ x y, herm G (γ x) (γ y) = herm G x y) ∧ I = γ.toLinearMap.graph) ∧
      (left I = ⊥ ↔ ∃! γ : GL (Fin N) E,
        (∀ x y, herm G (γ.1 *ᵥ x) (γ.1 *ᵥ y) = herm G x y) ∧
          ∀ x y, (x, y) ∈ I ↔ y = γ.1 *ᵥ x) ∧
      (∀ u : (Fin N → E) ≃ₗ[E] (Fin N → E),
        (∀ x ∈ (left I).orthogonalBilin (hermPairing G), u x - x ∈ left I) →
        I.map (u.toLinearMap.prodMap LinearMap.id) = I) ∧
      (∀ u : (Fin N → E) ≃ₗ[E] (Fin N → E),
        (∀ y ∈ (right I).orthogonalBilin (hermPairing G), u y - y ∈ right I) →
        I.map (LinearMap.id.prodMap u.toLinearMap) = I) ∧
      (∀ ξ ∈ left I, ∀ α : E,
        I.map ((Matrix.toLin' (transvMat G ξ α)).prodMap LinearMap.id) = I) ∧
      (∃! φ : Reduced (hermPairing G) (left I) ≃ₗ[E] Reduced (hermPairing G) (right I),
        (∀ a b, reducedForm (hermPairing G) (hermPairing_conj hG) (right I) (φ a) (φ b)
          = reducedForm (hermPairing G) (hermPairing_conj hG) (left I) a b) ∧
        I = glue (hermPairing G) (left I) (right I) φ)) ∧
    (∀ X X' : Submodule E (Fin N → E), (∀ x ∈ X, ∀ x' ∈ X, herm G x x' = 0) →
      (∀ y ∈ X', ∀ y' ∈ X', herm G y y' = 0) →
      ∀ φ : Reduced (hermPairing G) X ≃ₗ[E] Reduced (hermPairing G) X',
        (∀ a b, reducedForm (hermPairing G) (hermPairing_conj hG) X' (φ a) (φ b)
          = reducedForm (hermPairing G) (hermPairing_conj hG) X a b) →
        (∀ p ∈ glue (hermPairing G) X X' φ, ∀ q ∈ glue (hermPairing G) X X' φ,
          herm G p.1 q.1 - herm G p.2 q.2 = 0) ∧
        finrank E (glue (hermPairing G) X X' φ) = N ∧
        left (glue (hermPairing G) X X' φ) = X ∧ right (glue (hermPairing G) X X' φ) = X') := by sorry
