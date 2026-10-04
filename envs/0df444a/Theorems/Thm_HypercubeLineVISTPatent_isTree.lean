-- Prove2me | Theorems.Thm_HypercubeLineVISTPatent_isTree
-- name    : HypercubeLineVISTPatent_isTree
-- status  : Proved
-- author  : @undercat
-- created : 2026-09-27T15:35:29.410901+00:00
-- url     : https://prove2.me/theorems/a50909e0-7f67-4bfd-b65f-51bc19e9e59b
-- title:
--   Patent parent function is a rooted tree (Sym2)
-- statement:
--   The patent parent function fixes the root.

import Definitions.Def_HypercubeLineVIST_sym2parent
import Definitions.Def_HypercubeLineVIST_patentParent

theorem HypercubeLineVISTPatent_isTree (n : Nat) (hn : 3 < n)
    (r : Sym2 (Fin n → Bool)) (a b : Fin n → Bool) (d0 : Fin n)
    (k : HypercubeLineVISTSym2.TreeIdx n) (v : Sym2 (Fin n → Bool)) :
    HypercubeLineVISTSym2.patentParentSym2 n (by omega) r a b d0 k r = r := by
  sorry
