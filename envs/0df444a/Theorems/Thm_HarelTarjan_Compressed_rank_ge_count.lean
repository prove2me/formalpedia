-- Prove2me | Theorems.Thm_HarelTarjan_Compressed_rank_ge_count
-- name    : HarelTarjan.Compressed.rank_ge_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:54:52.749904+00:00
-- url     : https://prove2.me/theorems/50a11aff-3731-4620-a895-dbfaf90b8797
-- title:
--   Proof of Lemma 9, p. 345 — at most $n/2^{k-1}$ vertices have rank $k$ or greater
-- statement:
--   Let $T$ be a rooted tree on $n$ vertices and $C$ its compressed tree. For every $k \ge 0$, the number of vertices with rank $k$ or greater satisfies
--
--   $$\#\{\, v : \mathrm{rank}(v) \ge k \,\} \le \sum_{i=k}^{\infty} \frac{n}{2^i} = \frac{n}{2^{k-1}}.$$
--
--   This is the first sentence of the proof of Lemma 9 and yields the sizes of plies two and three.
--
--   **Formalization Note** The bound is stated without division as $\#\{v : \mathrm{rank}(v) \ge k\}\cdot 2^k \le 2n$, which is $n/2^{k-1}$ over the reals, including $k = 0$.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 345, proof of Lemma 9, first sentence

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_HarelTarjan_Compressed_HeavyPath
import Definitions.Def_HarelTarjan_Compressed_CompressedTree

namespace HarelTarjan.Compressed

theorem rank_ge_count {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V) (k : ℕ) :
    (Finset.univ.filter (fun v => k ≤ rank T v)).card * 2 ^ k ≤ 2 * Fintype.card V := by sorry

end HarelTarjan.Compressed
