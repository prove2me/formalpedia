-- Prove2me | Theorems.Thm_LSWCuttingPlane_SFMArcs_lemma_79
-- name    : LSWCuttingPlane.SFMArcs.lemma_79
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:43.046793+00:00
-- url     : https://prove2.me/theorems/aeb3dfcc-04e2-456e-99e0-94949a33f0c6
-- title:
--   Lemma 79 (new arc), p. 84 — if upper(p) > n⁴ maxⱼ yⱼ, some q ∉ R(p) lies in every minimizer that contains p
-- statement:
--   Let $f : 2^V \to \mathbb Z$ be submodular with $f(\emptyset) = 0$ on $V = [n]$, let $A$ be an acyclic set of arcs on $V$, and let $y = \sum_k \lambda^{(k)} y^{(k)}$ be a non-degenerate convex combination of BFS's $y^{(k)}$ of the base polyhedron $\mathcal B(f)$, each consistent with every arc of $A$. If some element $p$ satisfies
--
--   $$\mathrm{upper}(p) = f(R(p)) - f(R(p) - p) > n^4 \max_j y_j,$$
--
--   then there is $q \notin R(p)$ such that the arc $(p, q)$ is valid: every minimizer of $f$ over the ring family $\mathcal F_A$ that contains $p$ also contains $q$.
--
--   Adding the arc $(p, q)$ to $A$ shrinks the ring family while keeping a minimizer; since there are only $2\binom n2$ possible arcs, repeated application is what makes the paper's algorithms for submodular minimization strongly polynomial.
--
--   **Formalization Note** The paper's "$O(n)$" bound on the number of BFS's in the combination is dropped, since the existence claim holds for any finite convex combination and the count matters only for the oracle-call bound; the clause "using $O(n \cdot \mathrm{EO})$ oracle calls and $O(n^2)$ time" is out of scope. Validity is stated in the strong form "every minimizer containing $p$ contains $q$", which is the lemma's own gloss and what the proof shows; it implies the "for some minimizer" of p. 83. Non-degeneracy forces $n \ge 2$, so the hypothesis $n \ne 0$ (needed to write $\max_j y_j$) costs nothing. Indices are 0-based.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, p. 84, Lemma 79

import Mathlib
import Definitions.Def_LSWCuttingPlane_SFMArcs_Setting

namespace LSWCuttingPlane.SFMArcs

open Finset

/-- Lemma 79 (new arc), p. 84: let `y = ∑_k λ^{(k)} y^{(k)}` be a non-degenerate convex
combination of BFS's `y^{(k)}` of `B(f)` that are consistent with every arc of `A`. If some element
`p` satisfies `upper(p) > n⁴ max_j y_j`, then there is `q ∉ R(p)` such that the arc `(p, q)` is
valid: every minimizer of `f` over the ring family of `A` that contains `p` also contains `q`. -/
theorem lemma_79 {n : ℕ} [NeZero n] (f : Finset (Fin n) → ℤ) (hf : Submodular f) (hf0 : f ∅ = 0)
    (A : Fin n → Fin n → Prop) (hA : Acyclic A)
    {ι : Type} [Fintype ι] (lam : ι → ℝ) (σs : ι → Equiv.Perm (Fin n))
    (hcomb : IsConsistentComb A lam σs) (hnd : NonDegenerate (combo f lam σs))
    (p : Fin n) (hp : (n : ℝ) ^ 4 * ymax (combo f lam σs) < (upper f A p : ℝ)) :
    ∃ q, q ∉ R A p ∧ ∀ S : Finset (Fin n), IsMinimizer A f S → p ∈ S → q ∈ S := by sorry

end LSWCuttingPlane.SFMArcs
