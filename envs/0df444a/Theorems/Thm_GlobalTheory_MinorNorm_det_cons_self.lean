-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_det_cons_self
-- name    : GlobalTheory.MinorNorm.det_cons_self
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:28.783893+00:00
-- url     : https://prove2.me/theorems/4e271fdc-5055-4f75-9433-79ebaa0763d6
-- title:
--   Minor Norm: det cons self
-- statement:
--   The Minor Norm construction uses the det cons self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L52-L54

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

theorem GlobalTheory.MinorNorm.det_cons_self {m : ℕ} (M : Fin m → Fin (m + 1) → R) (t : Fin m) :
    (Matrix.of (Fin.cons (M t) M : Fin (m + 1) → Fin (m + 1) → R)).det = 0 := by sorry
