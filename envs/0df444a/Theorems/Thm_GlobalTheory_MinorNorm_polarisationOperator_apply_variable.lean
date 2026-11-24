-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_polarisationOperator_apply_variable
-- name    : GlobalTheory.MinorNorm.polarisationOperator_apply_variable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:27:36.331984+00:00
-- url     : https://prove2.me/theorems/4560a5df-e578-4200-93af-61830e5b421b
-- title:
--   Minor Norm: polarisation Operator apply variable
-- statement:
--   The Minor Norm construction uses the polarisation Operator apply variable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L98-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {k : ℕ} (x : Fin k → Fin k → R) (d : Fin k → Fin k → Derivation ℂ R R)
variable {x d}

theorem GlobalTheory.MinorNorm.polarisationOperator_apply_variable (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0) (i j s c : Fin k) :
    pol x d i j (x s c) = if c = j then x s i else 0 := by sorry
