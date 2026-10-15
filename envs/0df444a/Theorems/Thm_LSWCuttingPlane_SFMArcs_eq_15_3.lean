-- Prove2me | Theorems.Thm_LSWCuttingPlane_SFMArcs_eq_15_3
-- name    : LSWCuttingPlane.SFMArcs.eq_15_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:44.766378+00:00
-- url     : https://prove2.me/theorems/dbe97a2d-3e11-471c-9219-ff100faff79f
-- title:
--   (15.3), proof of Lemma 79, p. 85 — y′(V ∖ R(p)) ≤ y(V ∖ R(p) + p) − y′_p < (n − n⁴) maxⱼ yⱼ
-- statement:
--   Assume the hypotheses of Lemma 79: $f : 2^V \to \mathbb Z$ submodular with $f(\emptyset) = 0$ on $V = [n]$, $A$ an acyclic set of arcs, $y = \sum_k \lambda^{(k)} y^{(k)}$ a non-degenerate convex combination of BFS's consistent with $A$, and $p \in V$ with $\mathrm{upper}(p) > n^4 \max_j y_j$. Let $y' = \sum_k \lambda^{(k)} y'^{(k)}$, where $y'^{(k)}$ is the BFS whose defining permutation is that of $y^{(k)}$ with $R(p)$ moved to the front. Then
--
--   $$y'(V \setminus R(p)) \le y(V \setminus R(p) + p) - y'_p \qquad\text{and}\qquad y'(V \setminus R(p)) < (n - n^4) \max_j y_j. \tag{15.3}$$
--
--   Since $\max_j y_j > 0$, the right-hand side is negative, so some coordinate of $y'$ outside $R(p)$ is very negative; this is the input to Lemma 77.
--
--   **Formalization Note** $n$ and $n^4$ are real numbers here, so $n - n^4$ is not truncated. The intermediate lines of the display are not stated separately; the first and the last are.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, p. 85, proof of Lemma 79, display (15.3)

import Mathlib
import Definitions.Def_LSWCuttingPlane_SFMArcs_Setting

namespace LSWCuttingPlane.SFMArcs

open Finset

/-- Proof of Lemma 79, p. 85, display (15.3): under the hypotheses of Lemma 79, let `y′` be the
convex combination, with the same weights, of the BFS's whose defining permutations are those of
the `y^{(k)}` with `R(p)` moved to the front. Then
`y′(V \ R(p)) ≤ y(V \ R(p) + p) − y′_p` and `y′(V \ R(p)) < (n − n⁴) max_j y_j`. -/
theorem eq_15_3 {n : ℕ} [NeZero n] (f : Finset (Fin n) → ℤ) (hf : Submodular f) (hf0 : f ∅ = 0)
    (A : Fin n → Fin n → Prop) (hA : Acyclic A)
    {ι : Type} [Fintype ι] (lam : ι → ℝ) (σs τs : ι → Equiv.Perm (Fin n))
    (hcomb : IsConsistentComb A lam σs) (hnd : NonDegenerate (combo f lam σs))
    (p : Fin n) (hp : (n : ℝ) ^ 4 * ymax (combo f lam σs) < (upper f A p : ℝ))
    (hτ : ∀ k, IsFrontload (σs k) (R A p) (τs k)) :
    ysum (combo f lam τs) (Finset.univ \ R A p) ≤
        ysum (combo f lam σs) (insert p (Finset.univ \ R A p)) - combo f lam τs p ∧
    ysum (combo f lam τs) (Finset.univ \ R A p) <
        ((n : ℝ) - (n : ℝ) ^ 4) * ymax (combo f lam σs) := by sorry

end LSWCuttingPlane.SFMArcs
