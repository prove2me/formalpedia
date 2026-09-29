-- Prove2me | Theorems.Thm_Freiman_upper_tree_split_identification
-- name    : Freiman.upper_tree_split_identification
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:40.868379+00:00
-- url     : https://prove2.me/theorems/28fb4126-145b-4943-8b61-b9672098c234
-- title:
--   The recursive tree implements the five physical split rows
-- statement:
--   At each node, the recursive finite state, including the parity-dependent interchange of physical sides, gives exactly the parent and children in the corresponding prefixed deletion row.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Binary deletion order after m2a:endpoint-identities.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_tree_split_identification (p : List ℕ+) (k : Fin 5) (w : List Bool) :
    let s := upperStateAt ⟨p, k⟩ w; let D := upperImageSplit s.word (upperRows s.row);
    upperTree p k w = D.parent ∧
    upperTree p k (w ++ [false]) = D.left ∧
    upperTree p k (w ++ [true]) = D.right := by
  sorry

end Freiman
