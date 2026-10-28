-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_secondDifference_le_of_penalized_maxima_readable
-- name    : FunctionalInequalities.Analysis.secondDifference_le_of_penalized_maxima_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:48.480791+00:00
-- url     : https://prove2.me/theorems/a468a648-0c26-4aab-8d67-0b4ddb3e936a
-- title:
--   Global Second-Difference Bound from Penalized Maxima
-- statement:
--   This formalizes the algebraic second-difference estimate used in the weak Letwin route.
--
--   Let $E$ be finite-dimensional, let $u,V:E\to\mathbb R$ be differentiable, and assume:
--
--   1. $u$ is convex and bounded below by $m$;
--   2. $\kappa>0$ and $V(y)-\frac\kappa2\|y\|^2$ is convex;
--   3. $|DV(\nabla u(x))[\nabla u(x)]|\leq C$ for every $x$;
--   4. for every $\eta>0$, there exists $x_0$ such that the penalized second difference $\Delta_h^2u(y)-\eta u(y)$ is maximized at $x_0$, and
--      $$
--      (V\circ\nabla u-u)(x_0+h)+(V\circ\nabla u-u)(x_0-h)-2(V\circ\nabla u-u)(x_0)\leq\eta n.
--      $$
--
--   Then for every $x,h\in E$,
--
--   $$
--   \Delta_h^2u(x)\leq\frac{4\|h\|^2}{\kappa}.
--   $$
--
--   The result is a reusable global estimate once penalized maximizers with the stated comparison are available.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem secondDifference_le_of_penalized_maxima {u V : E → ℝ} (hconv : ConvexOn ℝ univ u)
--       (hu : Differentiable ℝ u) (hV : Differentiable ℝ V) {κ : ℝ} (hκ : 0 < κ)
--       (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2)) {C : ℝ}
--       (hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C) {m : ℝ} (hm : ∀ x, m ≤ u x)
--       (n : ℕ) (h : E)
--       (hmax : ∀ η > 0, ∃ x₀ : E,
--         (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
--           u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
--         (V (gradient u (x₀ + h)) - u (x₀ + h)) + (V (gradient u (x₀ - h)) - u (x₀ - h)) -
--           2 * (V (gradient u x₀) - u x₀) ≤ η * n) :
--       ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ 4 * ‖h‖ ^ 2 / κ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/SecondDifference`](https://prove2.me/theorems/5412cb80-13f4-48d5-ab21-d4aec90af26d).
--
--   Supporting theorems: [`sd_penalized_estimate`](https://prove2.me/theorems/c0c70d58-7455-4740-861b-7db419ae03b7).
--
--   Previous: [`sd_penalized_estimate`](https://prove2.me/theorems/c0c70d58-7455-4740-861b-7db419ae03b7) · Next: [`centeredDifference_contDiff_lipschitz_gradient`](https://prove2.me/theorems/4365f234-8db7-4310-8445-040bbe73e928).
--
--   [Source excerpt, lines 693–703](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L693-L703) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L687-L732 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondDifference`, declaration `FunctionalInequalities.Analysis.secondDifference_le_of_penalized_maxima`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondDifference

open Set
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.secondDifference_le_of_penalized_maxima_readable {u V : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (hu : Differentiable ℝ u) (hV : Differentiable ℝ V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2)) {C : ℝ}
    (hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C) {m : ℝ} (hm : ∀ x, m ≤ u x)
    (n : ℕ) (h : E)
    (hmax : ∀ η > 0, ∃ x₀ : E,
      (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
        u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
      (V (gradient u (x₀ + h)) - u (x₀ + h)) + (V (gradient u (x₀ - h)) - u (x₀ - h)) -
        2 * (V (gradient u x₀) - u x₀) ≤ η * n) :
    ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ 4 * ‖h‖ ^ 2 / κ := by sorry
