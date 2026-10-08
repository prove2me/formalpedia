-- Prove2me | Theorems.Thm_NashWilliams61_TreePacking_lemma_1
-- name    : NashWilliams61.TreePacking.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:47.863156+00:00
-- url     : https://prove2.me/theorems/df8255d2-0097-4fd6-9c3e-ab87518bd95f
-- title:
--   Lemma 1 — a tree on $W$ has $|W| - 1$ edges
-- statement:
--   Let $G$ be a finite multigraph without loops, and let $(W, T)$ be a tree in $G$: $W$ is a non-empty vertex set, every edge of $T$ has both ends in $W$, $T$ has no cycle, and any two vertices of $W$ are joined by a path of $T$-edges. Then
--   $$|T| = |W| - 1 .$$
--
--   This standard fact (Berge, *Théorie des graphes*, Ch. 16, Thm 1) is used in the proof of necessity of Theorem 1 and in the final count of the proof of sufficiency.
--
--   **Formalization Note** Stated as $|T| + 1 = |W|$ to avoid natural-number subtraction; the tree is in the multigraph sense (parallel edges form a cycle).
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 445, Lemma 1

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **Lemma 1** (Nash-Williams 1961, p. 445). `|E(T)| = |V(T)| − 1` for every tree `T`:
if `(W, T)` is a tree of the loopless multigraph, then `|T| + 1 = |W|`. -/
theorem lemma_1 {V E : Type} [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (W : Finset V) (T : Finset E) (hT : IsTreeOn ends W T) :
    T.card + 1 = W.card := by sorry

end NashWilliams61.TreePacking
