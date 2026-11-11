-- Prove2me | Theorems.Thm_IntervalExplore_KT1_lemma_3
-- name    : IntervalExplore.KT1.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:38.468729+00:00
-- url     : https://prove2.me/theorems/2dc7769c-5f82-4fb0-bf06-39c7fc90ea82
-- title:
--   Lemma 3 — distance to the next vertex in any ordering
-- statement:
--   Let $G'=(V',E')$ be a finite connected simple undirected graph with $n'\ge1$ vertices, ordered arbitrarily as $v_1,\ldots,v_{n'}$. Define $f(i)=\min_{j>i}d_{G'}(v_i,v_j)$ for $i<n'$. Then
--   $$
--   \sum_{i=1}^{n'-1}f(i)\le 2n'\log_2 n'.
--   $$
--   This graph-ordering inequality is the reusable geometric estimate for the vertex charges. It includes the singleton case, where both sides are zero.
--
--   Differences from the source:
--   - encoding: a vertex ordering v₁,...,vₙ′ and the sum over 1,...,n′-1 → an equivalence Fin n′ ≃ V′ and a sum over indices i with i.val+1<n′; reason: zero-based indexing includes exactly the same vertices and summands; the unused last-index infimum is zero
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Lemma 3, p.7 (PDF p.8)

import Definitions.Def_IntervalExplore_KT1_Rates

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- Lemma 3, p.7 (PDF p.8). Any vertex ordering; logarithm base two. -/
theorem lemma_3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (n : ℕ) (hn : 1 ≤ n) (enumeration : Fin n ≃ V) :
    (∑ i : Fin n, if i.val + 1 < n then (laterDistance G enumeration i : ℝ) else 0) ≤
      2 * n * Real.logb 2 n := by sorry

end IntervalExplore.KT1
