-- Prove2me | Theorems.Thm_NashWilliams61_TreePacking_lemma_4
-- name    : NashWilliams61.TreePacking.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:28:15.061296+00:00
-- url     : https://prove2.me/theorems/685d2b9a-57e4-4c1a-9783-73379455d40b
-- title:
--   Lemma 4 — pulling a spanning tree of $L - \xi$ back through fusions at $\xi$
-- statement:
--   Let $G = (V, F)$ be a finite multigraph without loops, $\xi \in V$, and $L = \Phi_1 \cdots \Phi_n G$, where $\Phi_1, \dots, \Phi_n$ are fusions at $\xi$ ($\Phi_n$ applied first, each $\Phi_i$ a fusion of $\Phi_{i+1} \cdots \Phi_n G$). Let $T$ be a spanning tree of $L - \xi$ (the subgraph of $L$ on $V \setminus \{\xi\}$ with the edges of $L$ not incident with $\xi$) which contains at least one of the new edges $\rho(\Phi_i)$, and let
--   $$U = \Phi_n^{-1} \cdots \Phi_1^{-1} T .$$
--   Then $V(U) = V$, and there is a set $A$ of edges of $U$, each incident with $\xi$, such that $U - A$ is a spanning tree of $G$.
--
--   In the closing argument of the paper, this converts each spanning tree of the supergraph $H$ that uses added edges into a spanning tree of $G$.
--
--   **Formalization Note** The fusions are a list `[Φ₁, …, Φₙ]` in an ambient edge type, with the validity condition of the definition file at every stage. "U − A is a spanning tree of G" is stated as two facts: $U$ has vertex set $V$, and its edge set minus $A$ is a spanning tree of $(V, F)$.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), pp. 447–448, Lemma 4

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_NashWilliams61_TreePacking_Fusions
open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **Lemma 4** (Nash-Williams 1961, pp. 447–448). Let `ξ ∈ V(G)`, `G = (V, F)`, and
`L = Φ₁ … Φₙ G` for fusions `Φᵢ` at `ξ` (the list `fs = [Φ₁, …, Φₙ]`, `Φₙ` applied first).
Let `T` be a spanning tree of `L − ξ` containing at least one `ρ(Φᵢ)`, and
`U = Φₙ⁻¹ … Φ₁⁻¹ T`. Then `V(U) = V(G)` and there is a set `A` of edges of `U` incident
with `ξ` such that `U − A` is a spanning tree of `G`. -/
theorem lemma_4 {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (F : Finset E) (ξ : V)
    (fs : List (Fusion V E)) (hξ : ∀ φ ∈ fs, φ.xi = ξ) (hfs : ValidList ends fs F)
    (T : Finset E)
    (hT : IsSpanningTreeOn ends (Finset.univ.erase ξ)
      ((applyList fs F).filter fun e => ξ ∉ ends e) T)
    (hρ : ∃ φ ∈ fs, φ.rho ∈ T) :
    (invList fs (Finset.univ.erase ξ, T)).1 = Finset.univ ∧
      ∃ A ⊆ (invList fs (Finset.univ.erase ξ, T)).2, (∀ e ∈ A, ξ ∈ ends e) ∧
        IsSpanningTreeOn ends Finset.univ F ((invList fs (Finset.univ.erase ξ, T)).2 \ A) := by sorry

end NashWilliams61.TreePacking
