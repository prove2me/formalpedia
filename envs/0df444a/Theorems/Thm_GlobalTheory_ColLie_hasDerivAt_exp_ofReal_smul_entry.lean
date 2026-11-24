-- Prove2me | Theorems.Thm_GlobalTheory_ColLie_hasDerivAt_exp_ofReal_smul_entry
-- name    : GlobalTheory.ColLie.hasDerivAt_exp_ofReal_smul_entry
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:56.452242+00:00
-- url     : https://prove2.me/theorems/d8d8ad2b-7154-4126-81de-c773cc8890fd
-- title:
--   Col Lie: has Deriv At exp of Real smul entry
-- statement:
--   The Col Lie construction uses the has Deriv At exp of Real smul entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtCoeffFockColumnSubstitutionExp.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtCoeffFockColumnSubstitutionExp.lean#L14-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ColLie
open GlobalTheory.MinorFrame
variable {ι : Type} [DecidableEq ι]

theorem GlobalTheory.ColLie.hasDerivAt_exp_ofReal_smul_entry {a : ℕ} (S : Matrix (Fin a) (Fin a) ℂ) (i j : Fin a) :
    HasDerivAt (fun h : ℝ => NormedSpace.exp ((h : ℂ) • S) i j) (S i j) 0 := by sorry
