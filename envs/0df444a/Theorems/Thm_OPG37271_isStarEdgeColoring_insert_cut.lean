-- Prove2me | Theorems.Thm_OPG37271_isStarEdgeColoring_insert_cut
-- name    : OPG37271.isStarEdgeColoring_insert_cut
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T05:05:51.043306+00:00
-- url     : https://prove2.me/theorems/068acc6d-ac57-4342-b95f-fc43db39ee14
-- title:
--   Cut-based star edge-coloring extension (Lemma 4.2(b))
-- statement:
--   Let $V(G) = A \sqcup B$ and let $X$ be the set of edges between $A$ and $B$. Suppose that an edge-coloring $c$ of $G$ restricts to a star edge-coloring on both $G[A]$ and $G[B]$, that no two distinct edges in $X$ share an endpoint in $A$ or have adjacent endpoints in $G[A]$, that every edge $e \in X$ receives a color distinct from all edges $e' \in G[B] \cup X$ ($e' \ne e$) at distance at most $2$ from $e$ in $G[B] \cup X$, and that every edge in $X$ receives a color distinct from every edge in $G[A]$. Then $c$ is a star edge-coloring of $G$.
-- source:
--   Dvořák, Mohar, and Šámal, Star chromatic index, J. Graph Theory 72 (2013), 313–326 (arXiv:1011.3376), Lemma 4.2(b).

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

universe u
namespace OPG37271

theorem isStarEdgeColoring_insert_cut {V : Type u} {G : SimpleGraph V} {K : Type*}
    (A : V → Prop) (c : EdgeColoring G K)
    (hcA : IsStarEdgeColoring (fun e => c ⟨Sym2.map Subtype.val e.1, by rcases e with ⟨⟨a, b⟩, hab⟩; exact hab⟩ :
      EdgeColoring (G.induce {v | A v}) K))
    (hcB : IsStarEdgeColoring (fun e => c ⟨Sym2.map Subtype.val e.1, by rcases e with ⟨⟨a, b⟩, hab⟩; exact hab⟩ :
      EdgeColoring (G.induce {v | ¬ A v}) K))
    (hX_sep : ∀ u₁ v₁ u₂ v₂ : V,
      G.Adj u₁ v₁ → A u₁ → ¬ A v₁ →
      G.Adj u₂ v₂ → A u₂ → ¬ A v₂ →
      s(u₁, v₁) ≠ s(u₂, v₂) →
      u₁ ≠ u₂ ∧ ¬ G.Adj u₁ u₂)
    (hX_B : ∀ u₁ v₁ x y : V,
      (h1 : G.Adj u₁ v₁) → A u₁ → ¬ A v₁ →
      (hxy : G.Adj x y) → (¬ A x ∨ ¬ A y) → s(x, y) ≠ s(u₁, v₁) →
      (x = u₁ ∨ x = v₁ ∨ y = u₁ ∨ y = v₁ ∨
        (G.Adj u₁ x ∧ ¬ A x) ∨ G.Adj v₁ x ∨ (G.Adj u₁ y ∧ ¬ A y) ∨ G.Adj v₁ y) →
      c.get x y hxy ≠ c.get u₁ v₁ h1)
    (hX_A : ∀ u₁ v₁ x y : V,
      (h1 : G.Adj u₁ v₁) → A u₁ → ¬ A v₁ →
      (hxy : G.Adj x y) → A x → A y →
      c.get x y hxy ≠ c.get u₁ v₁ h1) :
    IsStarEdgeColoring c := by sorry
end OPG37271
