-- Prove2me | Theorems.Thm_GlobalTheory_square_presentation_counital_comul_of_finrank
-- name    : GlobalTheory.square_presentation_counital_comul_of_finrank
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:11.35252+00:00
-- url     : https://prove2.me/theorems/221bd032-d20a-4156-b3f0-b2a5381f24a2
-- title:
--   Global Theory: square presentation counital comul of finrank
-- statement:
--   The Global Theory construction uses the square presentation counital comul of finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SquarePresentationOfCounitalComul.lean#L13-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SquarePresentationOfCounitalComul.lean#L13-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantDerivationOfCounitalComulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGeneratorsDualPointDerivationsAugmentedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationsDualToFamilyOfNilpotentAugStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedMonomialsLinearIndependentOverConstantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalTruncatedPolynomialPresentationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquarePresentationOfTowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusSubalgebraCounitalComulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquarePresentationOfCounitalComul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.square_presentation_counital_comul_of_finrank (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k)
      (Δ : A →ₐ[k] A ⊗[k] A), Module.finrank k A = n →
      ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧
        (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) →
      IsNilpotent (RingHom.ker ε) →
      (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k),
        Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by sorry
