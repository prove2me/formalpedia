-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_det_cons
-- name    : GlobalTheory.MinorNorm.det_cons
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:28:30.577293+00:00
-- url     : https://prove2.me/theorems/85cef059-b0a5-4d07-aa4f-15f83997ba47
-- title:
--   Minor Norm: det cons
-- statement:
--   The Minor Norm construction uses the det cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L46-L50

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

theorem GlobalTheory.MinorNorm.det_cons {m : ℕ} (v : Fin (m + 1) → R) (M : Fin m → Fin (m + 1) → R) :
    (Matrix.of (Fin.cons v M : Fin (m + 1) → Fin (m + 1) → R)).det =
      ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * v s * (Matrix.of fun t u => M t (s.succAbove u)).det := by sorry
