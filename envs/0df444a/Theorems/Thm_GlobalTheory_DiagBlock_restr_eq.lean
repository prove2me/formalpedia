-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_restr_eq
-- name    : GlobalTheory.DiagBlock.restr_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:44:22.404364+00:00
-- url     : https://prove2.me/theorems/4d3fbc1b-07f5-455b-96c8-1ce1d6e823a8
-- title:
--   Diag Block: restr eq
-- statement:
--   The Diag Block construction uses the restr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L15-L19

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

theorem GlobalTheory.DiagBlock.restr_eq {C : Type} [Field C] {n0 n : ℕ} (hn : n0 ≤ n) (G : MvPowerSeries (PVar n) C) :
    restr hn G = MvPowerSeries.killCompl ⟨embV hn, embV_inj hn⟩ G := by sorry
