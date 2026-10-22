-- Prove2me | Theorems.Thm_MaxEntTSP_Main_fact_2_1
-- name    : MaxEntTSP.Main.fact_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:17.302662+00:00
-- url     : https://prove2.me/theorems/c10d463f-6087-4c8d-9be4-3aff4c81f9ca
-- title:
--   Fact 2.1 — the rooted Held–Karp vector lies in the spanning-tree polytope
-- statement:
--   Let $x^0$ be a feasible Held–Karp vector with $x^0_{e_0}=1$, and let $E$ be its positive support after removing $e_0$. The restriction $x=x^0|_E$ satisfies the spanning-tree-polytope inequalities:
--   $$x(E)=|V|-1,\qquad x(E(S))\le |S|-1\quad(S\ne\varnothing),\qquad x_e\ge0\quad(e\in E).$$
--
--   This identifies the prescribed marginals as a convex combination of spanning-tree incidence vectors.
--
--   **Formalization Note** The printed display (2) includes $S=\varnothing$, where its bound would say $0\le-1$; this item uses nonempty $S$.
-- source:
--   Karlin, Klein & Oveis Gharan, A (Slightly) Improved Approximation Algorithm for Metric TSP, arXiv:2007.01409v6, p. 6 (PDF 8), Fact 2.1 and polytope (2)

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Cuts

namespace MaxEntTSP.Main

open MetricTSP Finset

/-- The rooted Held–Karp vector restricted away from `e₀` lies in (2). -/
theorem fact_2_1 (m : ℕ) (hm : 3 ≤ m) (x : Fin m → Fin m → ℝ)
    (hx : IsHeldKarp x) (a b : Fin m) (hab : a ≠ b) (he0 : x a b = 1) :
    let E := lpSupport x a b
    edgeMass x E = (m : ℝ) - 1 ∧
    (∀ S : Finset (Fin m), S.Nonempty →
      edgeMass x (internalEdges E S) ≤ (S.card : ℝ) - 1) ∧
    (∀ e ∈ E, 0 ≤ pairCost x e) := by sorry

end MaxEntTSP.Main
