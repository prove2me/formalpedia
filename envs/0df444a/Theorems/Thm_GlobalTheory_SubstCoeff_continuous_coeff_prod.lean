-- Prove2me | Theorems.Thm_GlobalTheory_SubstCoeff_continuous_coeff_prod
-- name    : GlobalTheory.SubstCoeff.continuous_coeff_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:08.456835+00:00
-- url     : https://prove2.me/theorems/6002820e-e4ae-4b6c-ad5a-99640c6885d2
-- title:
--   Subst Coeff: continuous coeff prod
-- statement:
--   The Subst Coeff construction uses the continuous coeff prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L29-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L29-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffMatrixFamilyBilateralSubstitutionMonomialCo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.SubstCoeff
variable {σ : Type}

theorem GlobalTheory.SubstCoeff.continuous_coeff_prod {Y κ : Type} [TopologicalSpace Y] (s : Finset κ) (f : κ → Y → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, Continuous fun y => coeff m (f q y)) (m : σ →₀ ℕ) :
    Continuous fun y => coeff m (∏ q ∈ s, f q y) := by sorry
