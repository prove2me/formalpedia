-- Prove2me | Theorems.Thm_LSWCuttingPlane_SFMArcs_lemma_77
-- name    : LSWCuttingPlane.SFMArcs.lemma_77
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:37.65248+00:00
-- url     : https://prove2.me/theorems/9952b5dc-8009-4b8d-ab1d-b2b1993664e3
-- title:
--   Lemma 77, p. 84 — if yᵢ < −(n − 1) maxⱼ yⱼ for a non-degenerate y ∈ B(f), i is in every minimizer
-- statement:
--   Let $f : 2^V \to \mathbb Z$ be submodular with $f(\emptyset) = 0$ on $V = [n]$, let $A$ be a set of arcs on $V$, and let $y \in \mathcal B(f)$ be non-degenerate. If $i \in V$ satisfies
--
--   $$y_i < -(n - 1) \max_j y_j,$$
--
--   then $i$ belongs to every minimizer of $f$ over the ring family $\mathcal F_A$.
--
--   Together with Lemma 76 this turns a single very negative (or very positive) coordinate of a point of the base polyhedron into a certificate about all minimizers.
--
--   **Formalization Note** $n - 1$ is computed in $\mathbb R$. The family $\mathcal F_A$ always contains $V$, which is all the proof needs of it; acyclicity of $A$ is not needed and not assumed.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, p. 84, Lemma 77

import Mathlib
import Definitions.Def_LSWCuttingPlane_SFMArcs_Setting

namespace LSWCuttingPlane.SFMArcs

open Finset

/-- Lemma 77, p. 84: if `y ∈ B(f)` is non-degenerate and satisfies `y_i < −(n − 1) max_j y_j`, then
`i` is in every minimizer of `f` over the ring family of `A`. -/
theorem lemma_77 {n : ℕ} [NeZero n] (f : Finset (Fin n) → ℤ) (hf : Submodular f) (hf0 : f ∅ = 0)
    (A : Fin n → Fin n → Prop) (y : Fin n → ℝ) (hB : y ∈ baseB f) (hnd : NonDegenerate y)
    (i : Fin n) (hi : y i < -((n : ℝ) - 1) * ymax y) :
    ∀ S : Finset (Fin n), IsMinimizer A f S → i ∈ S := by sorry

end LSWCuttingPlane.SFMArcs
