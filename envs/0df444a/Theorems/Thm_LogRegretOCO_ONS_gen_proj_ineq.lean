-- Prove2me | Theorems.Thm_LogRegretOCO_ONS_gen_proj_ineq
-- name    : LogRegretOCO.ONS.gen_proj_ineq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:35:30.734015+00:00
-- url     : https://prove2.me/theorems/5a866d81-50e4-428a-866a-7e877de73fbb
-- title:
--   Lemma 8 — generalized projections onto a convex set do not increase A-distances to points of the set
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^n$ be convex, let $A$ be a positive semidefinite $n\times n$ matrix, let $y\in\mathbb R^n$, and let $z=\Pi^{A}_{\mathcal P}(y)$ be a generalized projection of $y$ onto $\mathcal P$ with respect to $A$, i.e. $z\in\mathcal P$ minimises $(y-x)^\top A(y-x)$ over $x\in\mathcal P$. Then for every $a\in\mathcal P$,
--   $$
--   (y-a)^\top A\,(y-a)\ \ge\ (z-a)^\top A\,(z-a).
--   $$
--
--   This is the generalized Pythagorean inequality; in the analysis of the Online Newton Step it shows that the projection step can only decrease the $A_t$-distance to the comparator.
--
--   **Formalization Note** "Positive semidefinite" is Mathlib's `Matrix.PosSemidef` (symmetric with nonnegative quadratic form). The paper's display defines $\Pi^A_{\mathcal P}[y]$ with "min"; it means the minimising point (argmin), which is what the predicate encodes. No existence or uniqueness of the projection is assumed: the conclusion holds for every minimiser.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 188, Lemma 8

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic

namespace LogRegretOCO.ONS

/-- Lemma 8 (folklore; Hazan–Agarwal–Kale 2007, p. 188). Let `P ⊆ ℝⁿ` be convex, `A` positive
semidefinite, `y ∈ ℝⁿ`, and `z` a generalized projection of `y` onto `P` with respect to `A`.
Then `(y − a)ᵀ A (y − a) ≥ (z − a)ᵀ A (z − a)` for every `a ∈ P`. -/
theorem gen_proj_ineq {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (hP : Convex ℝ P)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (y z : EuclideanSpace ℝ (Fin n)) (hz : IsGenProj P A y z) :
    ∀ a ∈ P, quadForm A (z - a) ≤ quadForm A (y - a) := by sorry

end LogRegretOCO.ONS
