-- Prove2me | Theorems.Thm_GlobalTheory_SubstCoeff_isAlgebraic_coeff_one
-- name    : GlobalTheory.SubstCoeff.isAlgebraic_coeff_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:18.424948+00:00
-- url     : https://prove2.me/theorems/0a42b863-e72c-4800-975a-c9bf2acd2592
-- title:
--   Subst Coeff: is Algebraic coeff one
-- statement:
--   The Subst Coeff construction uses the is Algebraic coeff one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L53-L58

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

theorem GlobalTheory.SubstCoeff.isAlgebraic_coeff_one (m : σ →₀ ℕ) : IsAlgebraic ℚ (coeff m (1 : MvPolynomial σ ℂ)) := by sorry
