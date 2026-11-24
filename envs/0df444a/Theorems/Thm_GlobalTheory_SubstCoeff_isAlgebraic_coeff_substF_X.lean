-- Prove2me | Theorems.Thm_GlobalTheory_SubstCoeff_isAlgebraic_coeff_substF_X
-- name    : GlobalTheory.SubstCoeff.isAlgebraic_coeff_substF_X
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:18.741399+00:00
-- url     : https://prove2.me/theorems/b093fa54-e512-4ebe-8878-954177c524a2
-- title:
--   Subst Coeff: is Algebraic coeff subst F X
-- statement:
--   The Subst Coeff construction uses the is Algebraic coeff subst F X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L92-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L92-L103

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
variable {ι : Type} {N n : ℕ}

theorem GlobalTheory.SubstCoeff.isAlgebraic_coeff_substF_X (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hh : ∀ i a b, IsAlgebraic ℚ (h i a b)) (hg : ∀ i a b, IsAlgebraic ℚ (g i a b))
    (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    IsAlgebraic ℚ (coeff m (GlobalTheory.CompactHowe.substF h g (X q))) := by sorry
