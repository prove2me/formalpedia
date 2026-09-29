-- Prove2me | Theorems.Thm_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport
-- name    : MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/286f7e06-6185-544e-993a-ef6fd35e7022
-- title:
--   Parametric log integral: smooth A(p,ρ)+|ρ|B(p,ρ) decomposition
-- statement:
--   Let $P$ and $V$ be finite-dimensional real normed spaces, $V$ equipped with its Borel $\sigma$-algebra, and let $\mu$ be an additive Haar measure on $V$. Let $g : P \times (\mathbb{R} \times V) \to \mathbb{C}$ be $C^\infty$ with compact support, let $c_0 : P \to \mathbb{R}$ be $C^\infty$ with $c_0(p) \neq 0$ for every $p$, let $\varphi : P \to (V \to_{L[\mathbb{R}]} \mathbb{R})$ be a $C^\infty$ map into the continuous real-linear functionals on $V$, and let $\theta : P \times V \to \mathbb{R}$ be $C^\infty$ with $\theta(q) \geq 0$ for all $q$. The conclusion asserts the existence of two functions $A, B : P \times \mathbb{R} \to \mathbb{C}$, both $C^\infty$, such that for every $p \in P$ and every $\rho \in \mathbb{R}$ the function $$(s,v) \mapsto g(p,(s,v))\,\log\bigl((c_0(p)s + \varphi(p)(v))^2 + (\rho\,\theta(p,v))^2\bigr)$$ is integrable for the product measure of Lebesgue measure on $\mathbb{R}$ with $\mu$, and its integral over $\mathbb{R} \times V$ equals $A(p,\rho) + |\rho|\,B(p,\rho)$. Thus the $\rho$-dependence of the integral splits into a smooth part and $|\rho|$ times a smooth part, jointly smoothly in the parameter $p$.
--
--   This is the parametric form of the classical fact that a logarithmic potential $\log(s^2+\rho^2)$, integrated against a smooth compactly supported weight, is smooth in $\rho$ up to an explicit $|\rho|$-term; here the quadratic argument is allowed to depend on the parameter through a nowhere-vanishing coefficient $c_0$, a moving linear form $\varphi(p)$ on the transverse variable, and a non-negative smooth factor $\theta$ multiplying the offset $\rho$. It feeds the corresponding statement for arguments of the shape $(1-\lVert\cdot\rVert^2)^2 + \lVert \bar z + \bar r z\rVert^2$ arising at a complex place, the one-dimensional case and a smoothness criterion for parametric integrals of compactly supported smooth functions being the inputs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℝ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (c₀ : P → ℝ) (hc₀ : ContDiff ℝ (⊤ : ℕ∞) c₀) (hc₀0 : ∀ p, c₀ p ≠ 0)
    (φ : P → (V →L[ℝ] ℝ)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (θ : P × V → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθ0 : ∀ q, 0 ≤ θ q) :
    ∃ A B : P × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (p : P) (ρ : ℝ),
        Integrable (fun sv : ℝ × V =>
          g (p, sv) * (Real.log ((c₀ p * sv.1 + φ p sv.2) ^ 2 + (ρ * θ (p, sv.2)) ^ 2) : ℂ)) ((volume : Measure ℝ).prod μ) ∧
        ∫ sv : ℝ × V, g (p, sv) * (Real.log ((c₀ p * sv.1 + φ p sv.2) ^ 2 + (ρ * θ (p, sv.2)) ^ 2) : ℂ) ∂((volume : Measure ℝ).prod μ) =
          A (p, ρ) + ((|ρ| : ℝ) : ℂ) * B (p, ρ) := by sorry
