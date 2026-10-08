-- Prove2me | Theorems.Thm_Kakutani1941_FixedPoint_composition
-- name    : Kakutani1941.FixedPoint.composition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:15:34.432696+00:00
-- url     : https://prove2.me/theorems/ec0d5c5c-4872-4f5f-84b9-6e06ff1d59fa
-- title:
--   Proof of the Corollary — composition with the retraction
-- statement:
--   Let $S\subseteq S'$, let a continuous map $\psi:S'\to S$ be given, and let $\Phi$ be upper semi-continuous on $S$ with nonempty closed convex values contained in $S$. Then the correspondence $x\mapsto\Phi(\psi(x))$ is upper semi-continuous on $S'$, and for every $x\in S'$ its value $\Phi(\psi(x))$ is a nonempty closed convex subset of $S$, hence also of $S'$:
--
--   $$\Phi(\psi(x))\in\mathfrak R(S)\subseteq\mathfrak R(S')\qquad(x\in S').$$
--
--   This is the inheritance statement required to apply the simplex theorem on $S'$.
--
--   **Formalization Note** The page's "into $\mathfrak R(S)\subseteq\mathfrak R(S')$" is stated as two conclusions, values in $\mathfrak R(S)$ and values in $\mathfrak R(S')$. Nonemptiness is inherited and stated explicitly. The identity property of a retraction is not needed for this inheritance statement, so only continuity and the mapping property are assumed here.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), p. 458, proof of the Corollary, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib
import Definitions.Def_Kakutani1941_FixedPoint_ClosedConvexSubset
import Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous

namespace Kakutani1941.FixedPoint

/-- Proof of the Corollary, p. 458: the correspondence after retraction. -/
theorem composition {m : ℕ} {S T : Set (EuclideanSpace ℝ (Fin m))}
    (hST : S ⊆ T)
    (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hψcont : ContinuousOn ψ T) (hψmap : Set.MapsTo ψ T S)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦ : ∀ x ∈ S, IsClosedConvexSubset S (Φ x))
    (hΦne : ∀ x ∈ S, (Φ x).Nonempty)
    (husc : IsUpperSemicontinuous S Φ) :
    IsUpperSemicontinuous T (fun x => Φ (ψ x)) ∧
      (∀ x ∈ T, IsClosedConvexSubset S (Φ (ψ x))) ∧
      (∀ x ∈ T, IsClosedConvexSubset T (Φ (ψ x))) ∧
      (∀ x ∈ T, (Φ (ψ x)).Nonempty) := by sorry

end Kakutani1941.FixedPoint
