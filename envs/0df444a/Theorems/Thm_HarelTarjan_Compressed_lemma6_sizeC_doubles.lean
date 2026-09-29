-- Prove2me | Theorems.Thm_HarelTarjan_Compressed_lemma6_sizeC_doubles
-- name    : HarelTarjan.Compressed.lemma6_sizeC_doubles
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:53:22.207914+00:00
-- url     : https://prove2.me/theorems/de9abc71-d6a8-4393-9731-da05f15d1374
-- title:
--   Lemma 6 — every edge $v \to p_C(v)$ of $C$ satisfies $2\cdot\mathrm{size}_C(v) \le \mathrm{size}_C(p_C(v))$
-- statement:
--   Let $T$ be a rooted tree with root $r$ and $C$ its compressed tree. Every edge $v \to p_C(v)$ of $C$, that is, every vertex $v \ne r$, satisfies
--
--   $$2\cdot \mathrm{size}_C(v) \le \mathrm{size}_C(p_C(v)).$$
--
--   Sizes in $C$ at least double from child to parent. This is the fact behind the shallow depth of $C$ (Lemma 7) and the rank counting of Lemma 8.
--
--   **Formalization Note** The hypothesis $v \ne r$ expresses that $v \to p_C(v)$ is an edge of $C$; for the root, where the Lean map has $p_C(r) = r$, the inequality would be false.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 344, Lemma 6

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_HarelTarjan_Compressed_HeavyPath
import Definitions.Def_HarelTarjan_Compressed_CompressedTree

namespace HarelTarjan.Compressed

theorem lemma6_sizeC_doubles {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V) (v : V)
    (hv : v ≠ T.root) :
    2 * sizeC T v ≤ sizeC T (pC T v) := by sorry

end HarelTarjan.Compressed
