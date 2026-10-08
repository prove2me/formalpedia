-- Prove2me | Theorems.Thm_Kakutani1941_FixedPoint_retraction
-- name    : Kakutani1941.FixedPoint.retraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:03:04.242085+00:00
-- url     : https://prove2.me/theorems/34f22c17-20e7-4280-b97e-b9db37ae9a55
-- title:
--   Proof of the Corollary — continuous retraction onto a convex set
-- statement:
--   Let $S$ be a nonempty closed convex subset of Euclidean space, contained in a set $S'$. There is a mapping $\psi$ continuous on $S'$ that sends $S'$ into $S$ and fixes every point of $S$:
--
--   $$\psi(S')\subseteq S,\qquad \psi(x)=x\quad(x\in S).$$
--
--   This is the retracting map used to transfer the simplex result to an arbitrary bounded closed convex set.
--
--   **Formalization Note** The map is total on the ambient space, but only its restriction to $S'$ is constrained. Nonemptiness of $S$ is explicit so such a map can exist.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), p. 458, proof of the Corollary, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib

namespace Kakutani1941.FixedPoint

/-- Proof of the Corollary, p. 458: retraction of an enclosing simplex onto S. -/
theorem retraction {m : ℕ} {S T : Set (EuclideanSpace ℝ (Fin m))}
    (hSclosed : IsClosed S) (hSconvex : Convex ℝ S) (hSnonempty : S.Nonempty)
    (hST : S ⊆ T) :
    ∃ ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContinuousOn ψ T ∧ Set.MapsTo ψ T S ∧ ∀ x ∈ S, ψ x = x := by sorry

end Kakutani1941.FixedPoint
