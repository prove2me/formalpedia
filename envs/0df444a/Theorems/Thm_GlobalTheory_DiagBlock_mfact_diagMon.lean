-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_mfact_diagMon
-- name    : GlobalTheory.DiagBlock.mfact_diagMon
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:48:15.561389+00:00
-- url     : https://prove2.me/theorems/81c038e0-8536-4072-8f21-6771e8b9995d
-- title:
--   Diag Block: mfact diag Mon
-- statement:
--   The Diag Block construction uses the mfact diag Mon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L315-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L315-L342

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

theorem GlobalTheory.DiagBlock.mfact_diagMon {n0 n : ℕ} (L y : ℕ) :
    mfact (diagMon n0 n L y) = ((L * y).factorial * y.factorial) ^ (n - n0) := by sorry
