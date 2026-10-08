-- Prove2me | Theorems.Thm_Menger27_Curves_satz_beta
-- name    : Menger27.Curves.satz_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:25.343275+00:00
-- url     : https://prove2.me/theorems/a35632ac-bdf9-4973-8142-b1d83245b3eb
-- title:
--   Satz β — topological Menger theorem for compact regular spaces
-- statement:
--   Let $K$ be a compact metric space every point of which is regular, and let $P,Q\subseteq K$ be finite disjoint sets. If no set of fewer than $n$ points separates $P$ and $Q$ in $K$, then $K$ contains $n$ pairwise disjoint arcs, each joining $P$ to $Q$:
--   $$\exists\gamma_1,\dots,\gamma_n:\quad \gamma_i(0)\in P,\ \gamma_i(1)\in Q,\ \gamma_i([0,1])\cap\gamma_j([0,1])=\varnothing\quad(i\ne j).$$
--
--   This is the topological disjoint-arcs result used to establish Satz α. **Formalization Note** The printed Satz β does not assume that $K$ is connected or has finitely many components. Those assumptions are therefore absent here, although finite components are used during its proof.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 100, Satz β; proof on pp. 102–105

import Mathlib
import Definitions.Def_Menger27_Curves_Basic
import Definitions.Def_Menger27_Curves_Separation

namespace Menger27.Curves

/-- Satz β, p. 100: Menger's topological disjoint-arcs theorem. -/
theorem satz_beta {X : Type*} [MetricSpace X] [CompactSpace X]
    (hregular : ∀ p : X, IsRegularPoint p)
    (P Q : Finset X) (hdisj : Disjoint (P : Set X) (Q : Set X))
    (n : ℕ) (hconn : NPointConnected Set.univ (P : Set X) (Q : Set X) n) :
    ∃ γ : Fin n → unitInterval → X,
      (∀ i, IsArc (γ i) ∧ γ i 0 ∈ P ∧ γ i 1 ∈ Q) ∧
      ∀ i j, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j)) := by sorry

end Menger27.Curves
