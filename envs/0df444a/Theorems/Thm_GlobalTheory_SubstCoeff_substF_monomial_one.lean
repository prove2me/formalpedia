-- Prove2me | Theorems.Thm_GlobalTheory_SubstCoeff_substF_monomial_one
-- name    : GlobalTheory.SubstCoeff.substF_monomial_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:10.217111+00:00
-- url     : https://prove2.me/theorems/7040c247-4771-470a-b5fa-e2f3f7ec582b
-- title:
--   Subst Coeff: subst F monomial one
-- statement:
--   The Subst Coeff construction uses the subst F monomial one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L77-L81

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

theorem GlobalTheory.SubstCoeff.substF_monomial_one (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF h g (monomial k 1) = ∏ q ∈ k.support, (GlobalTheory.CompactHowe.substF h g (X q)) ^ k q := by sorry
