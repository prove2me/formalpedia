-- Prove2me | Theorems.Thm_MifflinSemismooth_Optimality_prop1_b
-- name    : MifflinSemismooth.Optimality.prop1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:10.203047+00:00
-- url     : https://prove2.me/theorems/291c76a1-7176-4c57-a866-e9321b384066
-- title:
--   Proposition 1(b), p. 3 — F⁰(x;d) = max [⟨g,d⟩ : g ∈ ∂F(x)]
-- statement:
--   Let $B\subseteq\mathbb R^n$ be open and let $F:\mathbb R^n\to\mathbb R$ be Lipschitz on $B$ with constant $K$. Let $x\in B$. Then for every direction $d\in\mathbb R^n$ the generalized directional derivative is attained as a maximum over the generalized gradient:
--   $$
--   F^0(x;d)=\max\,[\langle g,d\rangle : g\in\partial F(x)].
--   $$
--
--   The upper bound $\langle g,d\rangle\le F^0(x;d)$ is the definition of $\partial F(x)$; the content is that the bound is attained. In §5 this is used to turn values of $F^0$ into inner products with generalized gradients, for instance in the proof of Theorem 8.
--
--   **Formalization Note** "max" is `IsGreatest`, which asserts attainment and in particular $\partial F(x)\ne\emptyset$. The Lipschitz constant is $K\in\mathbb R_{\ge 0}$ (equivalent to the page's positive $K$). The same statement is drafted in mission I of this series.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 3, Proposition 1(b)

import Mathlib
import Definitions.Def_MifflinSemismooth_Optimality_Setting

namespace MifflinSemismooth.Optimality

/-- Mifflin (1976), §2, Proposition 1(b), p. 3: for `F` Lipschitz on an open set `B` and `x ∈ B`,
`F⁰(x; d) = max [⟨g, d⟩ : g ∈ ∂F(x)]`. -/
theorem prop1_b {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (B : Set (EuclideanSpace ℝ (Fin n)))
    (hB : IsOpen B) (K : NNReal) (hFB : LipschitzOnWith K F B) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ B) :
    ∀ d, IsGreatest ((fun g => inner ℝ g d) '' MifflinSemismooth.Extremal.genGrad F x)
      (ClarkeGradients.Shared.genDirDeriv F x d) := by sorry

end MifflinSemismooth.Optimality
