-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_diagMon_inl
-- name    : GlobalTheory.DiagBlock.diagMon_inl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:43:30.359883+00:00
-- url     : https://prove2.me/theorems/f83a0d69-19bc-4a4f-a09b-fe9a663977e7
-- title:
--   Diag Block: diag Mon inl
-- statement:
--   The Diag Block construction uses the diag Mon inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L268-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L268-L283

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

theorem GlobalTheory.DiagBlock.diagMon_inl (n0 n L y : ℕ) (ρ c : Fin n) :
    diagMon n0 n L y (Sum.inl (ρ, c)) = if n0 ≤ ρ.val ∧ c = ρ then L * y else 0 := by sorry
