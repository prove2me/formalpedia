-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_rowDeg_filter_le
-- name    : GlobalTheory.DiagBlock.rowDeg_filter_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:59.303323+00:00
-- url     : https://prove2.me/theorems/0c0ff59b-adaa-4203-8344-28147bcc4aea
-- title:
--   Diag Block: row Deg filter le
-- statement:
--   The Diag Block construction uses the row Deg filter le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L344-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L344-L349

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

theorem GlobalTheory.DiagBlock.rowDeg_filter_le {n : ℕ} (p : PVar n → Prop) [DecidablePred p] (m : PVar n →₀ ℕ) (ρ : Fin n) :
    rowDegZ (m.filter p) ρ ≤ rowDegZ m ρ ∧ rowDegZ' (m.filter p) ρ ≤ rowDegZ' m ρ := by sorry
