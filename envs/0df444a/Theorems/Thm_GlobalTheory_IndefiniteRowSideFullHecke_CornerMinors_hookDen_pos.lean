-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CornerMinors_hookDen_pos
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen_pos
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:19:15.152716+00:00
-- url     : https://prove2.me/theorems/1c726220-739a-4cff-8801-4d5094065ede
-- title:
--   Corner Minors: hook Den pos
-- statement:
--   The Corner Minors construction uses the hook Den pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/BottomMinor.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/BottomMinor.lean#L53-L61

import Mathlib
import Definitions.Def_Formalism_FockGram_StatementFock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
open MvPolynomial

theorem GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen_pos {l : ℕ} {a : Fin l → ℕ} (ha : Antitone a) :
    0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen a := by sorry
