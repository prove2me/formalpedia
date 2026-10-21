-- Prove2me | Theorems.Thm_LipBernoulli_MultiUtility_proposition_2_2
-- name    : LipBernoulli.MultiUtility.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:20.211342+00:00
-- url     : https://prove2.me/theorems/50da8625-ae28-47ba-8ccb-c69588b95cbe
-- title:
--   Proposition 2.2, p. 6 — KR(X) = {α(p − q)}, ‖α(p − q)‖_KR = αW1(p, q), ‖·‖_KR is a norm, finitely supported measures are dense
-- statement:
--   Let $X$ be a nonempty separable metric space with its Borel $\sigma$-algebra. Then
--
--   1. $\mathrm{KR}(X) = \{\alpha(p-q) : \alpha \ge 0 \text{ and } p, q \in \Delta_1(X)\}$, and for every $\alpha \ge 0$ and $p, q\in\Delta_1(X)$
--   $$
--   \|\alpha(p-q)\|_{\mathrm{KR}} = \alpha\, W_1(p,q);
--   $$
--   2. $\|\cdot\|_{\mathrm{KR}}$ is a norm on $\mathrm{KR}(X)$: it is finite, $\|\mu\|_{\mathrm{KR}} = 0$ only for $\mu = 0$, $\|\mu+\nu\|_{\mathrm{KR}} \le \|\mu\|_{\mathrm{KR}} + \|\nu\|_{\mathrm{KR}}$, and $\|c\mu\|_{\mathrm{KR}} = |c|\,\|\mu\|_{\mathrm{KR}}$ for real $c$;
--   3. the finitely supported measures in $\mathrm{KR}(X)$ are dense: for every $\mu \in \mathrm{KR}(X)$ and $\varepsilon > 0$ there is a finitely supported $\mu_0 \in \mathrm{KR}(X)$ with $\|\mu - \mu_0\|_{\mathrm{KR}} \le \varepsilon$.
--
--   This makes $\mathrm{KR}(X)$ a normed space spanned by differences of lotteries, in which the cone of a preorder can be separated by bounded linear functionals.
--
--   **Formalization Note** Nonemptiness of $X$ is added (the field's standing convention): for empty $X$, $\mathrm{KR}(X) = \{0\}$ while the right-hand side of (7) is empty. "Norm" is spelled out as finiteness on $\mathrm{KR}(X)$, definiteness, subadditivity and absolute homogeneity; the seminorm properties are called "clear" on p. 6. The KR norm is valued in $[0,\infty]$ and multiplication by $\alpha$, $|c|$ is through `ENNReal.ofReal`.
-- source:
--   Ok & Weaver, Lipschitz Bernoulli Utility Functions, arXiv:2104.11205v1, Proposition 2.2 and (7), p. 6

import Mathlib
import Definitions.Def_LipBernoulli_MultiUtility_Setting
import Definitions.Def_LipBernoulli_MultiUtility_KR

open MeasureTheory
open scoped ENNReal NNReal

namespace LipBernoulli.MultiUtility

/-- Proposition 2.2, p. 6. Let `X` be a (nonempty) separable metric space. Then
(7) `KR(X) = {α(p − q) : α ≥ 0 and p, q ∈ Δ₁(X)}`, with `‖α(p − q)‖_KR = α W₁(p, q)`;
`‖·‖_KR` is a norm on `KR(X)` (finite, definite, subadditive, absolutely homogeneous); and the
finitely supported measures in `KR(X)` are dense in `KR(X)` for this norm. -/
theorem proposition_2_2 {X : Type*} [MetricSpace X] [Nonempty X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X] :
    KR X = {σ | ∃ α : ℝ, 0 ≤ α ∧ ∃ p ∈ Delta1 X, ∃ q ∈ Delta1 X, σ = α • diff p q} ∧
    (∀ α : ℝ, 0 ≤ α → ∀ p ∈ Delta1 X, ∀ q ∈ Delta1 X,
      krNorm (α • diff p q) = ENNReal.ofReal α * W1 p q) ∧
    (∀ μ ∈ KR X, krNorm μ < ∞) ∧
    (∀ μ ∈ KR X, krNorm μ = 0 → μ = 0) ∧
    (∀ μ ∈ KR X, ∀ ν ∈ KR X, krNorm (μ + ν) ≤ krNorm μ + krNorm ν) ∧
    (∀ c : ℝ, ∀ μ ∈ KR X, krNorm (c • μ) = ENNReal.ofReal |c| * krNorm μ) ∧
    (∀ μ ∈ KR X, ∀ ε : ℝ, 0 < ε →
      ∃ μ₀ ∈ KR X, IsFinitelySupported μ₀ ∧ krNorm (μ - μ₀) ≤ ENNReal.ofReal ε) := by sorry

end LipBernoulli.MultiUtility
