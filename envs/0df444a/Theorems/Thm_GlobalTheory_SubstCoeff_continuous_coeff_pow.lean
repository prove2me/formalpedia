-- Prove2me | Theorems.Thm_GlobalTheory_SubstCoeff_continuous_coeff_pow
-- name    : GlobalTheory.SubstCoeff.continuous_coeff_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:18.811594+00:00
-- url     : https://prove2.me/theorems/116904c6-da36-4621-99fd-0c974c0de562
-- title:
--   Subst Coeff: continuous coeff pow
-- statement:
--   The Subst Coeff construction uses the continuous coeff pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L17-L27

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

theorem GlobalTheory.SubstCoeff.continuous_coeff_pow {Y : Type} [TopologicalSpace Y] (F : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => coeff m (F y)) (e : ℕ) (m : σ →₀ ℕ) :
    Continuous fun y => coeff m (F y ^ e) := by sorry
