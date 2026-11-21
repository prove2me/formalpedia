-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_hint_decode_correct
-- name    : LinearSetReconciliation327.Main.hint_decode_correct
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-20T13:08:24.404557+00:00
-- url     : https://prove2.me/theorems/0a2f9539-5c95-4a80-812b-b0ff01e68b73
-- title:
--   HintSketch tree decoder correctness
-- statement:
--   The HintSketch recursion-tree decoder is correct: if every node's capacity bounds hold, every node's input is a valid sparse instance, and the CR family recovers every sparse vector, then decoding the sketch of a set $x$ with hint $J$ returns exactly $x$.
-- source:
--   arXiv:2611.11409, §5.4 (HintSketch decoding) and §9.2 (top-level decoder); Theorem 6.5 (main guarantee), conjunct 8. Formal statement extracted verbatim from the Theorem 5.1 development (`Solutions/_51_zzz_full.lean`, §12.6).

import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_NodeValidity

namespace LinearSetReconciliation327.Main

theorem hint_decode_correct (CR : CRFamily) (hRec : CR.Recovers) :
    ∀ (T : Node), ∀ (X Y : ℕ) (r : Node.Seed T) (x J : Finset ℕ),
      Node.WF T X Y → Node.AllBounds T r x J → AllValid X Y T r x J →
        Node.decode CR T r (Node.sketch CR T r x) J = some x := by sorry

end LinearSetReconciliation327.Main
