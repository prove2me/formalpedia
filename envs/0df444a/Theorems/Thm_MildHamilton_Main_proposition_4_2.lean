-- Prove2me | Theorems.Thm_MildHamilton_Main_proposition_4_2
-- name    : MildHamilton.Main.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:51:04.37999+00:00
-- url     : https://prove2.me/theorems/f740daea-5f3d-4f6b-b8b8-d10582e91106
-- title:
--   Proposition 4.2, p. 7 — a router and a path forest give a Hamilton cycle
-- statement:
--   Let $D$ be a directed graph containing an $A,B$-Hamilton-router $S$. Suppose there is a directed path forest $\mathcal P$ with exactly $|A|=|B|$ paths, start-vertices in $B$, end-vertices in $A$, and internal vertices partitioning $V(D)\setminus V(S)$. Then $D$ has a Hamilton cycle.
--
--   This closes the final proof: the perfect matchings between layers supply the forest, and the router absorbs whatever bijection the forest induces.
--
--   **Formalization Note** The conclusion is a closed directed walk visiting each vertex exactly once, listed once. For a symmetric relation a list of two vertices is allowed by this directed notion, and is not a cycle of the undirected graph; the application has many vertices.
--
--   Differences from the source:
--   - encoding: a directed graph D containing a router S → an edge relation r on a nonempty finite type, and a vertex set W with IsHamiltonRouter r W A B; reason: a router on a subgraph of r is a router for r; the empty digraph has no Hamilton cycle to speak of
--   - encoding: a path forest with starts in B and ends in A → paths Q b from each b to τ b for a bijection τ : B ≃ A; reason: exactly |A| = |B| vertex-disjoint paths with these ends induce such a bijection
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Proposition 4.2, p. 7

import Mathlib
import Definitions.Def_MildHamilton_Main_Router

namespace MildHamilton.Main

/-- Proposition 4.2 (Muyesser, STOC 2027 submission #233, p. 7): a directed graph with edge relation `r`
containing an `A, B`-Hamilton-router on `W`, and a directed path forest of `|A| = |B|` paths `Q b`, from each
`b ∈ B` to `τ b ∈ A` with `τ` a bijection, whose internal vertices partition `V(D) \ W`, has a Hamilton cycle. -/
theorem proposition_4_2 {V : Type*} [Fintype V] [Nonempty V] (r : V → V → Prop) (W A B : Finset V)
    (hS : IsHamiltonRouter r W A B) (τ : B ≃ A) (Q : B → List V)
    (hpath : ∀ b : B, IsRPath r (b : V) (τ b : V) (Q b))
    (hdisj : ∀ b b' : B, b ≠ b' → List.Disjoint (interior (Q b)) (interior (Q b')))
    (hcover : ∀ v, v ∉ W ↔ ∃ b : B, v ∈ interior (Q b)) :
    ∃ l : List V, IsRHamiltonCycle r l := by sorry

end MildHamilton.Main
