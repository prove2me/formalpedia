-- Prove2me | Theorems.Thm_Menger27_Curves_satz_delta
-- name    : Menger27.Curves.satz_delta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:18:09.239176+00:00
-- url     : https://prove2.me/theorems/cd83ddae-2772-447d-8764-ccf92e1b7e86
-- title:
--   Satz δ — disjoint arcs in a finite arc complex
-- statement:
--   Let $K$ be a finite union of arcs whose pairwise intersections are limited to common endpoints. Let $P,Q\subseteq K$ be finite disjoint sets. If no subset of $K$ with fewer than $n$ points separates $P$ and $Q$, then $K$ contains $n$ pairwise disjoint arcs, each joining a point of $P$ to a point of $Q$:
--   $$\exists\gamma_1,\dots,\gamma_n\subseteq K:\quad\gamma_i(0)\in P,\ \gamma_i(1)\in Q,\ \gamma_i([0,1])\cap\gamma_j([0,1])=\varnothing\ (i\ne j).$$
--
--   This is Satz β for the ordinary one-dimensional spaces of p. 101. **Formalization Note** The source's standing convention takes $P$ and $Q$ disjoint; finite subsets of a metric space are closed. The arcs are injective.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), pp. 101–102, Satz δ and its proof

import Mathlib
import Definitions.Def_Menger27_Curves_Basic
import Definitions.Def_Menger27_Curves_Separation
import Definitions.Def_Menger27_Curves_Ordinary

namespace Menger27.Curves

/-- Satz δ, pp. 101–102: the finite arc-complex case of Satz β. -/
theorem satz_delta {X : Type*} [MetricSpace X]
    (K : Set X) (hK : OrdinaryOneDimensional K)
    (P Q : Finset X) (hP : (P : Set X) ⊆ K) (hQ : (Q : Set X) ⊆ K)
    (hdisj : Disjoint (P : Set X) (Q : Set X)) (n : ℕ)
    (hconn : NPointConnected K (P : Set X) (Q : Set X) n) :
    ∃ γ : Fin n → unitInterval → X,
      (∀ i, IsArc (γ i) ∧ γ i 0 ∈ P ∧ γ i 1 ∈ Q ∧
        Set.range (γ i) ⊆ K) ∧
      ∀ i j, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j)) := by sorry

end Menger27.Curves
