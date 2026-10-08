-- Prove2me | Theorems.Thm_MifflinSemismooth_Extremal_prop1_a
-- name    : MifflinSemismooth.Extremal.prop1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:34:19.468058+00:00
-- url     : https://prove2.me/theorems/f9cfef96-25a7-4a87-bcff-0c0ff4dec898
-- title:
--   Proposition 1(a), p. 3 — ∂F(x) is a nonempty convex compact set
-- statement:
--   Let $B\subseteq\mathbb R^n$ be open and let $F:\mathbb R^n\to\mathbb R$ be Lipschitz on $B$ with constant $K$. Let $x\in B$ and let $\partial F(x)=\{g:\langle g,d\rangle\le F^0(x;d)\ \forall d\}$ be the generalized gradient. Then
--
--   $$\partial F(x)\ \text{is a nonempty, convex, compact subset of}\ \mathbb R^n.$$
--
--   This is the basic regularity property of the generalized gradient, collected in the paper from Clarke; it makes maxima over $\partial F(x)$ attained and is used throughout the theory of semismooth functions.
--
--   **Formalization Note.** $\partial F$ is the support-set definition of the mission's `Basic` file. The Lipschitz constant is a nonnegative real; the page's positive $K$ is equivalent.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 3, Proposition 1(a)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_MifflinSemismooth_Extremal_Basic

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), Proposition 1(a), p. 3: for `F` Lipschitz on the open set `B` and `x ∈ B`,
`∂F(x)` is a nonempty convex compact subset of `ℝⁿ`. -/
theorem prop1_a {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (B : Set (EuclideanSpace ℝ (Fin n)))
    (hB : IsOpen B) (K : NNReal) (hFB : LipschitzOnWith K F B) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ B) :
    (genGrad F x).Nonempty ∧ Convex ℝ (genGrad F x) ∧ IsCompact (genGrad F x) := by sorry

end MifflinSemismooth.Extremal
