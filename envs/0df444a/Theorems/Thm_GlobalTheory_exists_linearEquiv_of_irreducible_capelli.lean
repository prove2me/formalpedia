-- Prove2me | Theorems.Thm_GlobalTheory_exists_linearEquiv_of_irreducible_capelli
-- name    : GlobalTheory.exists_linearEquiv_of_irreducible_capelli
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:56:31.246952+00:00
-- url     : https://prove2.me/theorems/f0251a44-660c-4df9-bf28-9ea17f7becf5
-- title:
--   Global Theory: exists linear Equiv of irreducible capelli
-- statement:
--   The Global Theory construction uses the exists linear Equiv of irreducible capelli property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLinearEquivOfIrreducibleCapelli.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLinearEquivOfIrreducibleCapelli.lean#L13-L35

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLinearEquivOfIrreducibleIsHW
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLinearEquivOfIrreducibleCapelli
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open GlobalTheory

theorem GlobalTheory.exists_linearEquiv_of_irreducible_capelli :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [AddCommGroup V₂]
      [Module ℂ V₂] [FiniteDimensional ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁)
      (E₂ : Fin n → Fin n → Module.End ℂ V₂) (m : Fin n → ℂ), GlRel E₁ → GlRel E₂ → Irr E₁ → Irr E₂ →
      (∀ w v, qdet E₁ w v = cpol m w • v) → (∀ w v, qdet E₂ w v = cpol m w • v) →
      ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by sorry
