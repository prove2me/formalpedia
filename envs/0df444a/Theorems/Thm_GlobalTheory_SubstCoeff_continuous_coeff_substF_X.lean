-- Prove2me | Theorems.Thm_GlobalTheory_SubstCoeff_continuous_coeff_substF_X
-- name    : GlobalTheory.SubstCoeff.continuous_coeff_substF_X
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:08.373281+00:00
-- url     : https://prove2.me/theorems/56bab530-4014-41c8-9527-85fa2d746989
-- title:
--   Subst Coeff: continuous coeff subst F X
-- statement:
--   The Subst Coeff construction uses the continuous coeff subst F X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCo.lean#L83-L90

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

theorem GlobalTheory.SubstCoeff.continuous_coeff_substF_X (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    Continuous fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) =>
      coeff m (GlobalTheory.CompactHowe.substF p.1 p.2 (X q)) := by sorry
