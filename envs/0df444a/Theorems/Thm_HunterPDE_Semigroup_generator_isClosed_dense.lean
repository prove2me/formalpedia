-- Prove2me | Theorems.Thm_HunterPDE_Semigroup_generator_isClosed_dense
-- name    : HunterPDE.Semigroup.generator_isClosed_dense
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:07:45.793311+00:00
-- url     : https://prove2.me/theorems/0f298bca-908c-4357-a4f8-1e1d35f4f713
-- title:
--   Theorem 5.32 — the generator of a C₀ semigroup is closed and densely defined
-- statement:
--   Let $X$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $\{T(t) : t \ge 0\}$ be a strongly continuous semigroup on $X$, and let $A : \mathcal{D}(A) \subset X \to X$ be its generator. Then $A$ is **closed** — its graph
--   $$G(A) = \{(f, Af) : f \in \mathcal{D}(A)\}$$
--   is a closed subset of $X \times X$ — and its domain $\mathcal{D}(A)$ is dense in $X$.
--
--   This is the first half of the necessity direction of the Hille–Yosida and Lumer–Phillips theorems.
--
--   **Formalization Note.** Closedness is Mathlib's `LinearPMap.IsClosed` (closed graph), the equivalent graph form of Definition 5.31 given on the same page.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 145, Theorem 5.32

import Mathlib
import Definitions.Def_HunterPDE_Semigroup_C0Semigroup

namespace HunterPDE.Semigroup

/-- Theorem 5.32 of Hunter, *Notes on PDEs* (p. 145). If `A` is the generator (Definition 5.30)
of a strongly continuous semigroup `{T(t)}` on a Banach space `X`, then `A` is closed (its graph
is closed in `X × X`, Definition 5.31) and its domain `D(A)` is dense in `X`. -/
theorem generator_isClosed_dense {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (T : ℝ → X →L[𝕜] X) (A : X →ₗ.[𝕜] X)
    (hT : IsC0Semigroup T) (hA : IsGenerator T A) :
    A.IsClosed ∧ Dense (A.domain : Set X) := by sorry

end HunterPDE.Semigroup
