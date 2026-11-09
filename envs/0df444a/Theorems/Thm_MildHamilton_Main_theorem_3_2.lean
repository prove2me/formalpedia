-- Prove2me | Theorems.Thm_MildHamilton_Main_theorem_3_2
-- name    : MildHamilton.Main.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:46.374279+00:00
-- url     : https://prove2.me/theorems/8190dee6-bf49-4421-b201-a3dbe7265271
-- title:
--   Theorem 3.2, p. 6 — Haxell's hypergraph matching theorem
-- statement:
--   Let $\mathcal H$ be a bipartite hypergraph with vertex partition $A\cup B$, where every edge $e$ satisfies $|e\cap A|=1$ and $|e\cap B|\le r-1$. For $S\subseteq A$, let $\mathcal H_S$ be the hypergraph on $B$ with edge set $\{e\cap B:e\in E(\mathcal H),\ e\cap S\ne\varnothing\}$. If
--
--   $$\tau(\mathcal H_S)>(2r-3)(|S|-1)\quad\text{for every }S\subseteq A,$$
--
--   then $\mathcal H$ has a matching saturating $A$.
--
--   This is the tool that turns Claim 1 into the vertex-disjoint paths of Lemma 3.1. The paper cites it from Haxell's 1995 article in the form of Asadpour, Feige and Saberi.
--
--   Differences from the source:
--   - encoding: edges e with |e ∩ A| = 1 and |e ∩ B| ≤ r − 1 → pairs (a, e ∩ B) with |e ∩ B| + 1 ≤ r; reason: a pair determines the edge; adding 1 avoids natural-number subtraction
--   - encoding: τ(H_S) > (2r − 3)(|S| − 1) → no set of at most that many vertices meets all edges of H_S, compared in ℤ; reason: τ may be infinite when an edge has empty trace on B, and the bound may be negative
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Theorem 3.2, p. 6

import Mathlib
import Definitions.Def_MildHamilton_Main_Hypergraph

namespace MildHamilton.Main

/-- Theorem 3.2, Haxell (Muyesser, STOC 2027 submission #233, p. 6). `|e ∩ B| ≤ r − 1` is written
`|e ∩ B| + 1 ≤ r`, and the bound `(2r − 3)(|S| − 1)` is computed in `ℤ`. -/
theorem theorem_3_2 {A B : Type*} [Fintype A] [Fintype B] (H : BipartiteHypergraph A B) (r : ℕ)
    (hedge : ∀ e ∈ H.edges, e.2.card + 1 ≤ r)
    (hτ : ∀ S : Finset A, TauGreaterThan (H.link S) ((2 * (r : ℤ) - 3) * ((S.card : ℤ) - 1))) :
    H.HasSaturatingMatching := by sorry

end MildHamilton.Main
