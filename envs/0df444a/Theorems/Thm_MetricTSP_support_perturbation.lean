-- Prove2me | Theorems.Thm_MetricTSP_support_perturbation
-- name    : MetricTSP.support_perturbation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-25T05:09:13.55974+00:00
-- url     : https://prove2.me/theorems/ac263e1b-8999-4011-a23f-fbbc6e8c64e7
-- title:
--   Balanced perturbation supported on a fractional perfect matching
-- statement:
--   **Existence of a balanced support perturbation.** Let $y$ be a strictly fractional perfect-matching-polytope point on an even vertex set $W$: symmetric, nonnegative, zero diagonal, supported inside $W$, with every degree $\sum_u y(v,u) = 1$ on $W$, every nonzero entry $< 1$, and every odd-cardinality subset $S \subseteq W$ cut by mass at least $1$. Then there is a **nonzero** symmetric perturbation $z$ with zero diagonal, supported on the support of $y$, whose row sums all vanish.
--
--   This is the combinatorial heart of the vertex analysis of the fractional matching polytope. Since every degree equals $1$ and every entry is $< 1$, each vertex of $W$ has at least two support-neighbours, so the support graph has minimum degree $\ge 2$ and contains a cycle. If some component were a bare **odd** cycle, its degree constraints would force all its entries to be $\tfrac12$ and its vertex set would be an odd set of $W$ cut by zero mass — contradicting the odd-cut hypothesis (it cannot be all of $W$ either, as $|W|$ is even). Hence the support contains an **even** closed walk in which some edge appears an odd number of times: either an even cycle, or two edge-disjoint odd cycles joined by a walk traversed once in each direction. Assigning alternating signs $\pm 1$ along such a walk produces the desired $z$: row sums cancel at every visit, and the odd-multiplicity edge receives an odd — hence nonzero — total coefficient.
--
--   This lemma supplies the perturbation step of `MetricTSP.pm_polytope_decomposition` (Edmonds' perfect matching polytope theorem), used by `MetricTSP.even_set_matching` in the proof of Wolsey's bound.
-- source:
--   J. Edmonds, Maximum matching and a polyhedron with 0,1-vertices, J. Res. Nat. Bur. Standards 69B (1965) 125-130; L. Lovász, M. D. Plummer, Matching Theory, North-Holland 1986, Chapter 7 (fractional matchings and basic solutions).

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem support_perturbation (n : ℕ) (W : Finset (Fin n)) (hW : Even W.card)
    (hWn : W.Nonempty)
    (y : Fin n → Fin n → ℝ) (hsym : ∀ u v, y u v = y v u)
    (hnn : ∀ u v, 0 ≤ y u v) (hdiag : ∀ v, y v v = 0)
    (hsupp : ∀ u v, y u v ≠ 0 → u ∈ W ∧ v ∈ W)
    (hdeg : ∀ v ∈ W, ∑ u, y v u = 1)
    (hfrac : ∀ u v, y u v ≠ 0 → y u v < 1)
    (hodd : ∀ S : Finset (Fin n), S ⊆ W → Odd S.card →
      1 ≤ ∑ u ∈ S, ∑ v ∈ W \ S, y u v) :
    ∃ z : Fin n → Fin n → ℝ, z ≠ 0 ∧ (∀ u v, z u v = z v u) ∧
      (∀ v, z v v = 0) ∧ (∀ u v, z u v ≠ 0 → y u v ≠ 0) ∧
      (∀ v, ∑ u, z v u = 0) := by sorry

end MetricTSP
