-- Prove2me | Theorems.Thm_GlobalTheory_SubstCoeff_isAlgebraic_coeff_prod
-- name    : GlobalTheory.SubstCoeff.isAlgebraic_coeff_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:08.97787+00:00
-- url     : https://prove2.me/theorems/3b469f65-9011-4960-823b-5bdb03f8f31a
-- title:
--   Subst Coeff: is Algebraic coeff prod
-- statement:
--   The Subst Coeff construction uses the is Algebraic coeff prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L69-L73

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

theorem GlobalTheory.SubstCoeff.isAlgebraic_coeff_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, IsAlgebraic ℚ (coeff m (f q))) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (coeff m (∏ q ∈ s, f q)) := by sorry
