-- Prove2me | Theorems.Thm_GlobalTheory_SubstCoeff_continuous_coeff_mul
-- name    : GlobalTheory.SubstCoeff.continuous_coeff_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:03.411627+00:00
-- url     : https://prove2.me/theorems/8acf0a6a-cfac-45bf-b344-4d0d0378c832
-- title:
--   Subst Coeff: continuous coeff mul
-- statement:
--   The Subst Coeff construction uses the continuous coeff mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L10-L15

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

theorem GlobalTheory.SubstCoeff.continuous_coeff_mul {Y : Type} [TopologicalSpace Y] (F G : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => coeff m (F y)) (hG : ∀ m, Continuous fun y => coeff m (G y)) (m : σ →₀ ℕ) :
    Continuous fun y => coeff m (F y * G y) := by sorry
