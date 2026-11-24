-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CornerMinors_nextPart_le
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:18:58.209333+00:00
-- url     : https://prove2.me/theorems/291e300d-7d6a-4a91-822f-c4c97e3d3e00
-- title:
--   Corner Minors: next Part le
-- statement:
--   The Corner Minors construction uses the next Part le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/BottomMinor.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/BottomMinor.lean#L45-L50

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart_le {l : ℕ} {a : Fin l → ℕ} (ha : Antitone a) (i : Fin l) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart a i ≤ a i := by sorry
