-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_det_cons_update
-- name    : GlobalTheory.MinorNorm.det_cons_update
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:24.122698+00:00
-- url     : https://prove2.me/theorems/c8dc6fe1-c27d-448a-b6f8-8bd34e1c13fe
-- title:
--   Minor Norm: det cons update
-- statement:
--   The Minor Norm construction uses the det cons update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L56-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L56-L72

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

theorem GlobalTheory.MinorNorm.det_cons_update {m : ℕ} (M : Fin m → Fin (m + 1) → R) (t : Fin m) (e : Fin (m + 1) → R) :
    (Matrix.of (Fin.cons (M t) (Function.update M t e) : Fin (m + 1) → Fin (m + 1) → R)).det =
      -(Matrix.of (Fin.cons e M : Fin (m + 1) → Fin (m + 1) → R)).det := by sorry
