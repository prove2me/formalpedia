-- Prove2me | Theorems.Thm_Kakutani1941_FixedPoint_limit_step
-- name    : Kakutani1941.FixedPoint.limit_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:15:55.284672+00:00
-- url     : https://prove2.me/theorems/64ebbd72-3993-43af-86c6-32d60e5435fa
-- title:
--   Proof of Theorem 1 — a limit of approximate fixed points
-- statement:
--   Let $S$ be a compact subset of Euclidean space and let $\Phi$ be upper semi-continuous on $S$, with closed convex values contained in $S$. Suppose that for every $\varepsilon>0$ there are approximation data with $r+1$ terms as defined above. Then
--
--   $$\exists x_0\in S\quad x_0\in\Phi(x_0).$$
--
--   This gives the compactness and convexity step in the proof of Theorem 1, independently of the subdivision that supplies the data.
--
--   **Formalization Note** Compactness makes explicit the property of the closed simplex used to take convergent subsequences. Nonempty values are not assumed because the approximation data already provide selections.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), p. 458, proof of Theorem 1, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib
import Definitions.Def_Kakutani1941_FixedPoint_ClosedConvexSubset
import Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous
import Definitions.Def_Kakutani1941_FixedPoint_ApproximationData

namespace Kakutani1941.FixedPoint

/-- Proof of Theorem 1, p. 458: limits of arbitrarily fine barycentric data. -/
theorem limit_step {m r : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hScompact : IsCompact S)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦ : ∀ x ∈ S, IsClosedConvexSubset S (Φ x))
    (husc : IsUpperSemicontinuous S Φ)
    (happrox : ∀ ε : ℝ, 0 < ε → ApproximationData S Φ r ε) :
    ∃ x₀ ∈ S, x₀ ∈ Φ x₀ := by sorry

end Kakutani1941.FixedPoint
