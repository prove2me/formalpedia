-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_exists_secondOrder_expansion_readable
-- name    : FunctionalInequalities.Analysis.ae_exists_secondOrder_expansion_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:21.597575+00:00
-- url     : https://prove2.me/theorems/5eb08b15-cdd6-4026-aca8-c20821e30f23
-- title:
--   Almost-Everywhere Alexandrov Expansion
-- statement:
--   This formalizes Alexandrov's second-order expansion theorem in the finite-dimensional inner-product setting.
--
--   Let $E$ be a finite-dimensional real inner-product space with measurable and Borel structures, and let $f:E\to\mathbb R$ be convex on all of $E$. For almost every $x$ with respect to Lebesgue measure, there exist $p\in E$ and a continuous linear map $B:E\to E$ such that:
--
--   1. $B$ is symmetric:
--      $$\langle Bv,w\rangle=\langle v,Bw\rangle\qquad(v,w\in E).$$
--   2. $p$ is the unique subgradient of $f$ at $x$.
--   3. For every $\varepsilon>0$, for all $y$ sufficiently near $x$,
--      $$\left|f(y)-f(x)-\langle p,y-x\rangle-\frac12\langle B(y-x),y-x\rangle\right|\le \varepsilon\|y-x\|^2.$$
--
--   The declaration `ae_exists_secondOrder_expansion_readable` is the main almost-everywhere second-order expansion interface for later convex-analytic arguments. The almost-everywhere quantifier is with respect to `volume`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_exists_secondOrder_expansion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {f : E → ℝ}
--       (hconv : ConvexOn ℝ univ f) :
--       ∀ᵐ x ∂(volume : Measure E), ∃ p : E, ∃ B : E →L[ℝ] E,
--         (∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫) ∧
--         (∀ q : E, (∀ y, f x + ⟪q, y - x⟫ ≤ f y) → q = p) ∧
--         ∀ ε > 0, ∀ᶠ y in 𝓝 x,
--           |f y - f x - ⟪p, y - x⟫ - (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/SecondOrder`](https://prove2.me/theorems/25ef7ab1-0f22-4192-9c58-d196bc21f161).
--
--   Selected supporting theorems: [`eventually_abs_sub_quadratic_le_of_subgradient_expansion`](https://prove2.me/theorems/4ddfd262-d82d-4fdf-95dc-67ccaaffbd1b), [`exists_subgradient_slope_le_inner_add`](https://prove2.me/theorems/030b4fd7-878c-4020-bf9d-be7e6b77019e), [`inner_hasFDerivAt_resolvent_symm`](https://prove2.me/theorems/403fd5b6-c99c-485d-b4de-1d3af30e51e9), [`lipschitzWith_proximalPoint`](https://prove2.me/theorems/400fd9e1-fb0c-4e87-8ab5-d48890ee12a0), [`subgradient_expansion_of_hasFDerivAt_resolvent`](https://prove2.me/theorems/87eddc48-68f3-46a2-9e7f-49882aba3799).
--
--   Previous: [`integral_mul_le_integral_mul_sum_iteratedFDeriv`](https://prove2.me/theorems/a34ffeae-071d-4fec-b551-07733fa204a2).
--
--   [Source excerpt, lines 600–607](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L600-L607) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L596-L678 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondOrder`, declaration `FunctionalInequalities.Analysis.ae_exists_secondOrder_expansion`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder

open scoped RealInnerProductSpace Topology
open MeasureTheory Set Filter

theorem FunctionalInequalities.Analysis.ae_exists_secondOrder_expansion_readable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂(volume : Measure E), ∃ p : E, ∃ B : E →L[ℝ] E,
      (∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫) ∧
      (∀ q : E, (∀ y, f x + ⟪q, y - x⟫ ≤ f y) → q = p) ∧
      ∀ ε > 0, ∀ᶠ y in 𝓝 x,
        |f y - f x - ⟪p, y - x⟫ - (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by sorry
