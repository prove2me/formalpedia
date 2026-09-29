-- Prove2me | Theorems.Thm_HarelTarjan_Compressed_lemma8_rank_count
-- name    : HarelTarjan.Compressed.lemma8_rank_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:54:28.071018+00:00
-- url     : https://prove2.me/theorems/23a79d67-b13d-41af-9cd1-2869b26e152a
-- title:
--   Lemma 8 — for any rank $i$, the number of vertices of rank $i$ is at most $n/2^i$
-- statement:
--   Let $T$ be a rooted tree on $n$ vertices and $C$ its compressed tree, with $\mathrm{rank}(v) = \lfloor \lg \mathrm{size}_C(v)\rfloor$. For every $i \ge 0$,
--
--   $$\#\{\, v : \mathrm{rank}(v) = i \,\} \le \frac{n}{2^i}.$$
--
--   Few vertices have high rank. Summed over $i \ge k$ this gives the count of high-rank vertices used for Lemma 9.
--
--   **Formalization Note** The bound is stated without division as $\#\{v : \mathrm{rank}(v) = i\}\cdot 2^i \le n$, which is equivalent over the reals.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 344, Lemma 8

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_HarelTarjan_Compressed_HeavyPath
import Definitions.Def_HarelTarjan_Compressed_CompressedTree

namespace HarelTarjan.Compressed

theorem lemma8_rank_count {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V) (i : ℕ) :
    (Finset.univ.filter (fun v => rank T v = i)).card * 2 ^ i ≤ Fintype.card V := by sorry

end HarelTarjan.Compressed
