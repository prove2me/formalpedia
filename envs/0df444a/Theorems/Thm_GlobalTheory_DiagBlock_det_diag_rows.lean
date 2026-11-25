-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_det_diag_rows
-- name    : GlobalTheory.DiagBlock.det_diag_rows
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:52.165469+00:00
-- url     : https://prove2.me/theorems/7d0bcb13-24f7-42ff-afa1-573813cf029e
-- title:
--   Diag Block: det diag rows
-- statement:
--   The Diag Block construction uses the det diag rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L82-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L82-L110

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock

theorem GlobalTheory.DiagBlock.det_diag_rows {A : Type} [CommRing A] {n0 n : ℕ} (hn : n0 ≤ n) (M : Matrix (Fin n) (Fin n) A)
    (hM : ∀ ρ c : Fin n, n0 ≤ ρ.val → c ≠ ρ → M ρ c = 0) :
    M.det = (M.submatrix (Fin.castLE hn) (Fin.castLE hn)).det *
      ∏ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => n0 ≤ ρ.val), M ρ ρ := by sorry
