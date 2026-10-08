-- Prove2me | Theorems.Thm_MifflinSemismooth_Extremal_prop1_b
-- name    : MifflinSemismooth.Extremal.prop1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:35:17.573134+00:00
-- url     : https://prove2.me/theorems/6192c683-5230-4b50-9dc2-c33f0bea9952
-- title:
--   Proposition 1(b), p. 3 — F⁰(x;d) = max [⟨g,d⟩ : g ∈ ∂F(x)]
-- statement:
--   Let $B\subseteq\mathbb R^n$ be open and let $F:\mathbb R^n\to\mathbb R$ be Lipschitz on $B$ with constant $K$. Let $x\in B$. Then for every direction $d\in\mathbb R^n$ the generalized directional derivative is the largest value of $\langle g,d\rangle$ over the generalized gradient, and this largest value is attained:
--
--   $$F^0(x;d)=\max\{\langle g,d\rangle:\ g\in\partial F(x)\}.$$
--
--   So $F^0(x;\cdot)$ is the support function of $\partial F(x)$. In the proof of Theorem 2 this identity is applied to the extremal function $E$.
--
--   **Formalization Note.** "max" is `IsGreatest` of the image of $\partial F(x)$ under $g\mapsto\langle g,d\rangle$, asserting both the bound and its attainment. The Lipschitz hypothesis also ensures that the real `limsup` defining $F^0$ is not a default value.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 3, Proposition 1(b)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_MifflinSemismooth_Extremal_Basic

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), Proposition 1(b), p. 3: for `F` Lipschitz on the open set `B` and `x ∈ B`,
`F⁰(x; d) = max [⟨g, d⟩ : g ∈ ∂F(x)]` for every `d`. -/
theorem prop1_b {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (B : Set (EuclideanSpace ℝ (Fin n)))
    (hB : IsOpen B) (K : NNReal) (hFB : LipschitzOnWith K F B) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ B) :
    ∀ d, IsGreatest ((fun g => inner ℝ g d) '' genGrad F x)
      (ClarkeGradients.Shared.genDirDeriv F x d) := by sorry

end MifflinSemismooth.Extremal
