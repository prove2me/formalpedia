-- Prove2me | Theorems.Thm_GlobalTheory_SubstCoeff_isAlgebraic_coeff_pow
-- name    : GlobalTheory.SubstCoeff.isAlgebraic_coeff_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:15.748484+00:00
-- url     : https://prove2.me/theorems/f578bb00-0a26-405f-9a15-948ab89cb824
-- title:
--   Subst Coeff: is Algebraic coeff pow
-- statement:
--   The Subst Coeff construction uses the is Algebraic coeff pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L60-L67

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

theorem GlobalTheory.SubstCoeff.isAlgebraic_coeff_pow (P : MvPolynomial σ ℂ)
    (hP : ∀ m, IsAlgebraic ℚ (coeff m P)) (e : ℕ) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (coeff m (P ^ e)) := by sorry
