-- Prove2me | Theorems.Thm_Kakutani1941_FixedPoint_kakutani_fixed_point
-- name    : Kakutani1941.FixedPoint.kakutani_fixed_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:15:34.584295+00:00
-- url     : https://prove2.me/theorems/982fe7f0-c22a-4da7-a4a3-fdfdcdc6013a
-- title:
--   Corollary — Kakutani fixed point theorem for bounded closed convex sets
-- statement:
--   Let $S$ be a nonempty bounded closed convex subset of a Euclidean space. Suppose that $\Phi$ is upper semi-continuous on $S$ and that every value $\Phi(x)$, for $x\in S$, is a nonempty closed convex subset of $S$. Then
--
--   $$\exists x_0\in S\quad x_0\in\Phi(x_0).$$
--
--   The Corollary extends Theorem 1 from a simplex to any bounded closed convex domain in Euclidean space. It is the mission's goal and the form used in Kakutani's subsequent intersection theorem.
--
--   **Formalization Note** The paper's value family $\mathfrak R(S)$ includes empty sets; the nonemptiness of $S$ and all values is explicit here. The ambient space is $\mathbb R^m$ with its Euclidean norm, including $m=0$. Values outside $S$ are irrelevant.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), p. 458, Corollary to Theorem 1, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib
import Definitions.Def_Kakutani1941_FixedPoint_ClosedConvexSubset
import Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous

namespace Kakutani1941.FixedPoint

/-- Corollary, p. 458: Kakutani's theorem on a bounded closed convex set. -/
theorem kakutani_fixed_point {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hSbounded : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hSconvex : Convex ℝ S) (hSnonempty : S.Nonempty)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦ : ∀ x ∈ S, IsClosedConvexSubset S (Φ x))
    (hΦne : ∀ x ∈ S, (Φ x).Nonempty)
    (husc : IsUpperSemicontinuous S Φ) :
    ∃ x₀ ∈ S, x₀ ∈ Φ x₀ := by sorry

end Kakutani1941.FixedPoint
