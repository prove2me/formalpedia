-- Prove2me | Theorems.Thm_GlobalTheory_T_hasDerivAt_coeff_fockColumnSubstitution_exp
-- name    : GlobalTheory.T.hasDerivAt_coeff_fockColumnSubstitution_exp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:34:07.864357+00:00
-- url     : https://prove2.me/theorems/7a773766-4876-5425-9ea6-f5e14284bc66
-- title:
--   T: has Deriv At coeff fock Column Substitution exp
-- statement:
--   The T construction uses the has Deriv At coeff fock Column Substitution exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtCoeffFockColumnSubstitutionExpStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtCoeffFockColumnSubstitutionExpStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExp
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExpStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasDerivAt_coeff_fockColumnSubstitution_exp : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a)
    (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
    HasDerivAt (fun h : ℝ => MvPolynomial.coeff m (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R))
      (MvPolynomial.coeff m (GlobalTheory.ColLie.colDer τ S R)) 0 := by sorry
