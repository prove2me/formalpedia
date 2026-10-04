-- Prove2me | Theorems.Thm_NumStochOpt_QuasiFejer_eq_6_13_bias_gamma
-- name    : NumStochOpt.QuasiFejer.eq_6_13_bias_gamma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T20:34:38.461474+00:00
-- url     : https://prove2.me/theorems/867203fe-2b67-4af8-a1ef-36c840fd83cd
-- title:
--   Eq. (6.13) — a biased stochastic subgradient satisfies (6.12) with γ₀(s) = −⟨b⁰(s), x* − x^s⟩
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R$, $X\subseteq\mathbb R^n$ with optimal set $X^*$, and let $x^s$, $\xi^0(s)$ be random vectors on a probability space. Suppose the direction $\xi^0(s)$ satisfies (6.5):
--   $$
--   E\{\xi^0(s)\mid x^0,\dots,x^s\}=F_x(x^s)+b^0(s)\quad\text{a.s.},
--   $$
--   where $F_x(x^s)$ is a subgradient of $F$ at $x^s$ relative to $X$, i.e. $F(z)-F(x^s)\ge\langle F_x(x^s),z-x^s\rangle$ for all $z\in X$ (almost surely), and $b^0(s)$ is a random bias vector. Then for every $x^*\in X^*$, almost surely,
--   $$
--   F(x^*)-F(x^s)\ge\langle E\{\xi^0(s)\mid x^0,\dots,x^s\},x^*-x^s\rangle+\gamma^0(s),\qquad \gamma^0(s)=-\langle b^0(s),x^*-x^s\rangle,
--   $$
--   which is the quasigradient condition (6.12) with the error term (6.13).
--
--   It shows that (6.12) covers stochastic subgradients with a bias. On a bounded $X$, $|\gamma^0(s)|\le\|b^0(s)\|\operatorname{diam}X$, which gives an error term not depending on $x^*$, as used in Theorem 6.2.
--
--   **Formalization Note** The subgradient property is taken relative to $X$, as in the book's definition on p. 141. The book writes $F^\nu$, $b^\nu$ with $\nu=0$; here $F$, $b$.
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 143, Eq. (6.13) (with Eq. (6.5), p. 142, and the subgradient inequality, p. 141)

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.QuasiFejer

/-- **Eq. (6.13)** (Ermoliev, Ch. 6 of Ermoliev & Wets (1988), p. 143). If the direction `ξ⁰(s)`
satisfies (6.5), i.e. `E{ξ⁰(s) | x⁰, …, x^s} = F_x(x^s) + b⁰(s)` almost surely with `F_x(x^s)` a
subgradient of `F` at `x^s` relative to `X`, then the quasigradient inequality (6.12) holds for
every `x* ∈ X*` with `γ⁰(s) = -⟨b⁰(s), x* - x^s⟩`. -/
theorem eq_6_13_bias_gamma {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ g b : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (s : ℕ)
    (hsub : ∀ᵐ ω ∂μ, ∀ y ∈ X, F y - F (x s ω) ≥ ⟪g s ω, y - x s ω⟫_ℝ)
    (h65 : condExp (historySigma x s) μ (ξ s) =ᵐ[μ] fun ω => g s ω + b s ω) :
    ∀ xstar ∈ optimalSet F X, ∀ᵐ ω ∂μ,
      F xstar - F (x s ω) ≥
        ⟪(condExp (historySigma x s) μ (ξ s)) ω, xstar - x s ω⟫_ℝ + (-⟪b s ω, xstar - x s ω⟫_ℝ) := by sorry

end NumStochOpt.QuasiFejer
