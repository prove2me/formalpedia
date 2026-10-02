-- Prove2me | Theorems.Thm_HunterPDE_Semigroup_lumer_phillips
-- name    : HunterPDE.Semigroup.lumer_phillips
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:10:18.860976+00:00
-- url     : https://prove2.me/theorems/773ca588-f7c0-4e9b-af29-73e09e1876a7
-- title:
--   Theorem 5.38 — Lumer–Phillips theorem
-- statement:
--   Let $X$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ and $A : \mathcal{D}(A) \subset X \to X$ a linear operator. Then $A$ is the generator of a strongly continuous contraction semigroup on $X$ if and only if
--
--   1. $A$ is closed and densely defined, and
--   2. $A$ is m-dissipative: for every real $\lambda > 0$,
--   $$\lambda\|f\| \le \|(\lambda I - A) f\| \qquad \text{for all } f \in \mathcal{D}(A),$$
--   and $\lambda I - A$ maps $\mathcal{D}(A)$ onto $X$ for some $\lambda > 0$.
--
--   The Lumer–Phillips theorem replaces the resolvent estimates of the Hille–Yosida theorem by an energy inequality and a solvability condition for one resolvent equation, which is how semigroup generation is usually verified for PDEs (for example, for the Laplacian on $H^2(\mathbb{R}^n) \subset L^2(\mathbb{R}^n)$).
--
--   **Formalization Note.** "Generator" is Definition 5.30: the left side says there is a strongly continuous contraction semigroup whose generator equals $A$, domain included. Operators are Mathlib's partially defined linear maps `X →ₗ.[𝕜] X`; closedness is closedness of the graph.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 147, Theorem 5.38

import Mathlib
import Definitions.Def_HunterPDE_Semigroup_C0Semigroup
import Definitions.Def_HunterPDE_Semigroup_Resolvent

namespace HunterPDE.Semigroup

/-- Theorem 5.38 (Lumer–Phillips) of Hunter, *Notes on PDEs* (p. 147). An operator
`A : D(A) ⊂ X → X` in a Banach space `X` (over `𝕜 = ℝ` or `ℂ`) is the generator of a contraction
semigroup on `X` if and only if (1) `A` is closed and densely defined; (2) `A` is m-dissipative
(Definition 5.37). "Generator" is Definition 5.30: the generator's domain is exactly where the
right difference quotient converges, so the left side says `A` equals, domain included, the
generator of some strongly continuous contraction semigroup. -/
theorem lumer_phillips {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (A : X →ₗ.[𝕜] X) :
    (∃ T : ℝ → X →L[𝕜] X, IsContractionSemigroup T ∧ IsGenerator T A) ↔
      (A.IsClosed ∧ Dense (A.domain : Set X)) ∧ IsMDissipative A := by sorry

end HunterPDE.Semigroup
