-- Prove2me | Theorems.Thm_LSWCuttingPlane_SFMArcs_eq_15_2
-- name    : LSWCuttingPlane.SFMArcs.eq_15_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:43.763008+00:00
-- url     : https://prove2.me/theorems/733be04a-e3a5-492f-927d-d5f5114bcd63
-- title:
--   (15.2), proof of Lemma 79, p. 85 — moving R(p) to the front gives y′_p = upper(p), y′ ≥ y on R(p), y′ ≤ y off R(p)
-- statement:
--   Let $f : 2^V \to \mathbb Z$ be submodular with $f(\emptyset) = 0$, let $A$ be an acyclic set of arcs on $V$, and let $\sigma$ be a permutation of $V$ consistent with $A$; let $y$ be the BFS of $\sigma$. Fix $p \in V$. Then there is a permutation $\tau$ obtained from $\sigma$ by moving $R(p)$ to the front (preserving the relative order of the elements of $R(p)$ and of those outside $R(p)$), and for every such $\tau$ the BFS $y'$ of $\tau$ satisfies
--
--   $$y'_p = \mathrm{upper}(p) = f(R(p)) - f(R(p) - p), \qquad y'_j \ge y_j \ \ \forall j \in R(p), \qquad y'_j \le y_j \ \ \forall j \notin R(p). \tag{15.2}$$
--
--   This is the comparison the proof of Lemma 79 makes for each BFS of the convex combination; averaging with the weights $\lambda^{(k)}$ gives the same statement for the combinations $y$ and $y'$.
--
--   **Formalization Note** The paper states (15.2) for the convex combinations; it is formalized here for one defining permutation, from which the combined version follows because the weights are non-negative. The existence of the moved permutation is part of the statement so that the universally quantified part is not vacuous.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, p. 85, proof of Lemma 79, display (15.2)

import Mathlib
import Definitions.Def_LSWCuttingPlane_SFMArcs_Setting

namespace LSWCuttingPlane.SFMArcs

open Finset

/-- Proof of Lemma 79, p. 85, display (15.2), for one defining permutation `σ` consistent with
`A`: the permutation `τ` obtained from `σ` by moving `R(p)` to the front (preserving the relative
order inside `R(p)` and outside it) exists, and for every such `τ` the BFS `y′` of `τ` and the
BFS `y` of `σ` satisfy `y′_p = upper(p)`, `y′_j ≥ y_j` for `j ∈ R(p)` and `y′_j ≤ y_j` for
`j ∉ R(p)`. -/
theorem eq_15_2 {n : ℕ} (f : Finset (Fin n) → ℤ) (hf : Submodular f) (hf0 : f ∅ = 0)
    (A : Fin n → Fin n → Prop) (hA : Acyclic A) (σ : Equiv.Perm (Fin n))
    (hσ : Consistent A σ) (p : Fin n) :
    (∃ τ : Equiv.Perm (Fin n), IsFrontload σ (R A p) τ) ∧
    ∀ τ : Equiv.Perm (Fin n), IsFrontload σ (R A p) τ →
      bfs f τ p = (upper f A p : ℝ) ∧
      (∀ j ∈ R A p, bfs f σ j ≤ bfs f τ j) ∧
      (∀ j ∉ R A p, bfs f τ j ≤ bfs f σ j) := by sorry

end LSWCuttingPlane.SFMArcs
