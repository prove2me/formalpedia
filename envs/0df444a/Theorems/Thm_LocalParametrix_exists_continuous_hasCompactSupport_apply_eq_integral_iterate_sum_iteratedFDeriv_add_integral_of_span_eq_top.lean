-- Prove2me | Theorems.Thm_LocalParametrix_exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top
-- name    : LocalParametrix.exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/307ea134-762f-5f6c-b6e3-74a6083cebb9
-- title:
--   Local fundamental solution with continuous kernels near x₀
-- statement:
--   Let $E$ be a finite-dimensional real normed space, with its Borel structure, and let $\mu$ be an additive Haar measure on $E$. Let $\iota$ be a finite index type, let $A\colon\iota\to(E\to_{L}E)$ be a family of continuous linear endomorphisms of $E$, and let $x_0\in E$ be a point at which the vectors $A_i x_0$ span $E$ over $\mathbb{R}$, i.e. $\operatorname{span}_{\mathbb{R}}\{A_i x_0 : i\in\iota\}=\top$. Let $m$ be a natural number with $\operatorname{finrank}_{\mathbb{R}}E<2m$, and let $V$ be a neighbourhood of $x_0$. Write $\mathcal{L}$ for the operator sending $G\colon E\to\mathbb{C}$ to the function $y\mapsto\sum_{i}D^2G(y)(A_iy,\dots,A_iy)$, the second iterated Fréchet derivative of $G$ at $y$ evaluated at the constant tuple with entries $A_iy$. The assertion is that there exist $g_1,g_2\colon E\to\mathbb{C}$, both continuous with compact support and with $\operatorname{tsupport} g_1\subseteq V$ and $\operatorname{tsupport} g_2\subseteq V$, such that for every $F\colon E\to\mathbb{C}$ which is $C^\infty$ and compactly supported, $$F(x_0)=\int_E (\mathcal{L}^{m}F)(x)\,g_1(x)\,d\mu(x)+\int_E F(x)\,g_2(x)\,d\mu(x),$$ where $\mathcal{L}^{m}$ is the $m$-fold iterate of $\mathcal{L}$.
--
--   The spanning hypothesis makes $\mathcal{L}$ elliptic at $x_0$, and the statement is a local parametrix, or local fundamental solution, for $\mathcal{L}^m$ with continuous kernel $g_1$ and continuous remainder $g_2$, both localised in a prescribed neighbourhood of $x_0$; in distributional terms ${}^t(\mathcal{L}^m)g_1=\delta_{x_0}-g_2$, the dimension condition $\dim E<2m$ guaranteeing continuity rather than mere local integrability of the kernel. It is obtained from the global version on an inner product space together with a cut-off mechanism for operators that are smooth off a point, and it is used in the construction of conjugation-invariant archimedean test functions expressed as sums of integrals against such kernels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalParametrix_exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Topology

theorem LocalParametrix.exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] (A : ι → E →L[ℝ] E) (x₀ : E)
    (hA : Submodule.span ℝ (Set.range fun i => A i x₀) = ⊤)
    (m : ℕ) (hm : Module.finrank ℝ E < 2 * m) (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, ((fun (G : E → ℂ) (y : E) =>
                  ∑ i, iteratedFDeriv ℝ 2 G y (fun _ => A i y))^[m] F) x * g₁ x ∂μ) +
          ∫ x, F x * g₂ x ∂μ := by sorry
