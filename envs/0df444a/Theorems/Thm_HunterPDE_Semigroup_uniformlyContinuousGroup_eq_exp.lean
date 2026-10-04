-- Prove2me | Theorems.Thm_HunterPDE_Semigroup_uniformlyContinuousGroup_eq_exp
-- name    : HunterPDE.Semigroup.uniformlyContinuousGroup_eq_exp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:07:00.987412+00:00
-- url     : https://prove2.me/theorems/405dfe16-3d79-4431-b991-13d2a92e061c
-- title:
--   Theorem 5.24 — a uniformly continuous group is e^{tA} with A = T′(0) bounded
-- statement:
--   Let $X$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ and let $\{T(t) : t \in \mathbb{R}\}$ be a uniformly continuous group on $X$: $T(0) = I$, $T(s)T(t) = T(s+t)$ for all $s,t$, and $\|T(h) - I\| \to 0$ as $h \to 0$. Then
--
--   1. $T \in C^\infty(\mathbb{R}; \mathcal{L}(X))$;
--   2. $A = T'(0)$ exists in $\mathcal{L}(X)$, i.e. is a bounded linear operator on $X$;
--   3. for every $t \in \mathbb{R}$,
--   $$T(t) = e^{tA} = \sum_{n=0}^{\infty} \frac{t^n}{n!} A^n .$$
--
--   Thus norm continuity alone forces the group to be the exponential of a bounded generator; unbounded generators (as for the heat equation) only arise for strongly continuous families.
--
--   **Formalization Note.** $X$ is also given a compatible real normed-space structure (`[NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]`) so that $t \mapsto T(t)$ can be differentiated in the real variable $t$; for $\mathbb{K} = \mathbb{R}$ the two structures coincide. Clauses (2) and (3) are stated together as: there is $A \in \mathcal{L}(X)$ with $T'(0) = A$ and $T(t) = e^{tA}$ for all $t$. $C^\infty$ is `ContDiff ℝ ∞`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 141, Theorem 5.24

import Mathlib
import Definitions.Def_HunterPDE_Semigroup_C0Semigroup

open scoped ContDiff

namespace HunterPDE.Semigroup

/-- Theorem 5.24 of Hunter, *Notes on PDEs* (p. 141). If `{T(t) : t ∈ ℝ}` is a uniformly
continuous group on a Banach space `X` (over `𝕜 = ℝ` or `ℂ`), then
(1) `T ∈ C^∞(ℝ; L(X))`; (2) `A = T′(0)` is a bounded linear operator on `X`;
(3) `T(t) = e^{tA}` for every `t ∈ ℝ`.

Clause (2) is the existence of the derivative `A ∈ L(X)` of `t ↦ T(t)` at `0` in the operator
norm; (3) is stated for that `A`, with `e^{tA}` the exponential series (5.17) in `L(X)`.
`[NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]` only make `X` a real space compatibly with its
`𝕜`-structure, so that `t ↦ T(t)` can be differentiated in the real variable `t`. -/
theorem uniformlyContinuousGroup_eq_exp {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
    [CompleteSpace X] (T : ℝ → X →L[𝕜] X) (hT : IsUniformlyContinuousGroup T) :
    ContDiff ℝ ∞ T ∧
      ∃ A : X →L[𝕜] X, HasDerivAt T A 0 ∧ ∀ t : ℝ, T t = NormedSpace.exp (t • A) := by sorry

end HunterPDE.Semigroup
