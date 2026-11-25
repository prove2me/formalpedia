-- Prove2me | Theorems.Thm_GlobalTheory_ConnPointwise_entry_le_of_mulVec
-- name    : GlobalTheory.ConnPointwise.entry_le_of_mulVec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:44.517204+00:00
-- url     : https://prove2.me/theorems/07067863-3b29-4fa8-b6e8-b063b07cb74c
-- title:
--   Conn Pointwise: entry le of mul Vec
-- statement:
--   The Conn Pointwise construction uses the entry le of mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConnectionMatrixGramOperatorNormLe.lean#L97-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConnectionMatrixGramOperatorNormLe.lean#L97-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.ConnPointwise
variable {g : ℕ}

theorem GlobalTheory.ConnPointwise.entry_le_of_mulVec (P : Matrix (Fin g) (Fin g) ℝ) {W : ℝ} (hW : 0 ≤ W)
    (h : ∀ x, ‖P *ᵥ x‖ ≤ W * ‖x‖) (j k : Fin g) : |P j k| ≤ W := by sorry
