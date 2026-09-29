-- Prove2me | Theorems.Thm_HarelTarjan_Compressed_lemma5_sizeC
-- name    : HarelTarjan.Compressed.lemma5_sizeC
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:52:49.764658+00:00
-- url     : https://prove2.me/theorems/45bfec94-4e35-42c0-a258-c7ce843bade0
-- title:
--   Lemma 5 — $\mathrm{size}_C(v) = \mathrm{size}_T(v)$ at an apex, and $\mathrm{size}_C(v) = 1$ otherwise
-- statement:
--   Let $T$ be a rooted tree and $C$ its compressed tree. For every vertex $v$:
--
--   $$\mathrm{size}_C(v) = \begin{cases} \mathrm{size}_T(v) & \text{if } v \text{ is an apex},\\ 1 & \text{if } v \text{ is not an apex.}\end{cases}$$
--
--   So compression keeps the subtree of every apex intact (all its $T$-descendants become its $C$-descendants), while a vertex strictly inside a heavy path becomes a leaf of $C$. This is the first structural fact about $C$ and leads to the size doubling of Lemma 6.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 344, Lemma 5

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_HarelTarjan_Compressed_HeavyPath
import Definitions.Def_HarelTarjan_Compressed_CompressedTree

namespace HarelTarjan.Compressed

theorem lemma5_sizeC {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V) (v : V) :
    (IsApex T v → sizeC T v = size T v) ∧ (¬ IsApex T v → sizeC T v = 1) := by sorry

end HarelTarjan.Compressed
