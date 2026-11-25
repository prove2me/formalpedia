-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_diagMon_inr
-- name    : GlobalTheory.DiagBlock.diagMon_inr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:44:11.088977+00:00
-- url     : https://prove2.me/theorems/d55b6a8f-07a0-4075-8f25-050b22c00957
-- title:
--   Diag Block: diag Mon inr
-- statement:
--   The Diag Block construction uses the diag Mon inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L285-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L285-L300

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

theorem GlobalTheory.DiagBlock.diagMon_inr (n0 n L y : ℕ) (ρ c : Fin n) :
    diagMon n0 n L y (Sum.inr (ρ, c)) = if n0 ≤ ρ.val ∧ c = ρ then y else 0 := by sorry
