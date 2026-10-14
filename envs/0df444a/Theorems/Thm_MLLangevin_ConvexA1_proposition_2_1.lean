-- Prove2me | Theorems.Thm_MLLangevin_ConvexA1_proposition_2_1
-- name    : MLLangevin.ConvexA1.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:26.574667+00:00
-- url     : https://prove2.me/theorems/05e9d486-68d5-4649-92dd-179bcb0bcd29
-- title:
--   Proposition 2.1, p. 9 — under (C_α), (H₁)–(H₄) hold for 𝔞 = 1, δ = 1/2 with max(αc₂²/L², αc₃²/L², c₄²) ≲_uc Υ₁²
-- statement:
--   There is a universal constant $\mathfrak c_u$ with the following property. Let $b$ be $L$-Lipschitz and satisfy $(\mathbf C_\alpha)$ with $\alpha\in(0,L\wedge1]$, let $\sigma>0$, $W$ a standard $d$-dimensional Brownian motion, $\pi$ an invariant probability of the diffusion $X^x_t=x+\int_0^tb(X^x_s)ds+\sigma W_t$, $x_0\in\mathbb R^d$ and $\eta_0\in(0,\frac\alpha{2L^2}\wedge\frac12]$. Then there are constants $c_2,c_3,c_4$ such that, with
--   $$c_1(x)=|x-x_0|+\sqrt{|b(x_0)|^2\Big(\frac1{L^2}+\frac2{\alpha^2}\Big)+\frac{2\sigma^2d}\alpha},$$
--
--   1. $(\mathbf H_1)$ holds with $c_1$, rate $\alpha$ and $\eta_0$, for every Lipschitz $f$;
--   2. $(\mathbf H_2)$ holds with $\mathfrak a=1$ and $c_2$;
--   3. $(\mathbf H_3)$ holds with $\delta=\frac12$ and $c_3$, for every Lipschitz $f$ integrable under $\pi$;
--   4. $(\mathbf H_4)$ holds with $c_1$ and $c_4$;
--   5. and
--   $$\max\Big(\frac{\alpha c_2^2}{L^2},\frac{\alpha c_3^2}{L^2},c_4^2\Big)\le\mathfrak c_u\,\Upsilon_1^2,\qquad\Upsilon_1^2=1\vee\big(\alpha^{-2}|b(x_0)|^2+\alpha^{-1}\sigma^2d\big).$$
--
--   This verifies, with explicit dependence on $d$, $\alpha$, $L$, $\sigma$ and $b(x_0)$, all the assumptions of the general multilevel complexity theorem in the strongly contractive additive case.
--
--   **Formalization Note** The page prints $c_1(x)\le|x-x_0|^2+\sqrt{2|b(x_0)|^2(\frac1{L^2}+\frac2{\alpha^2})+\frac{\sigma^2d}\alpha}$; its proof (p. 35) takes $c_1$ from Lemma 5.1 (ii) with $x^\star=x_0$, which is the function used here. $\lesssim_{uc}$ is a constant quantified before every datum; $c_2,c_3,c_4$ are chosen after the data.
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, Proposition 2.1 and (12), p. 9; proof §5.2, p. 35

import Mathlib
import Definitions.Def_MLLangevin_ConvexA1_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

/-- Proposition 2.1, p. 9: under (C_α) with `α ∈ (0, L ∧ 1]` and `η₀ ∈ (0, α/(2L²) ∧ 1/2]`,
(H₁)–(H₄) hold with `𝔞 = 1`, `δ = 1/2`, `c₁` of Lemma 5.1 (ii) at `x⋆ = x₀`, and
`max(αc₂²/L², αc₃²/L², c₄²) ≲_uc Υ₁²`. -/
theorem proposition_2_1 : ∃ cu : ℝ, ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d) (_hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ) (_hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (_hC : CondC b α) (_hα : 0 < α) (_hαL : α ≤ L) (_hα1 : α ≤ 1) (_hσ : 0 < σ)
    (Xsol : SDEState d → ℝ≥0 → Ω → SDEState d) (_hX : ∀ x, IsAddSolution b σ W x (Xsol x))
    (π : Measure (SDEState d)) [IsProbabilityMeasure π] (_hπ : IsInvDiffusion P Xsol π)
    (x₀ : SDEState d) (η₀ : ℝ) (_hη₀ : 0 < η₀) (_hη₀' : η₀ ≤ min (α / (2 * L ^ 2)) (1 / 2)),
    ∃ c₂ c₃ c₄ : ℝ,
      (∀ f : SDEState d → ℝ, (∃ K, LipschitzWith K f) →
        H1 P b σ W f α η₀ (c1fun b σ α L x₀)) ∧
      H2 P b σ W x₀ η₀ 1 c₂ ∧
      (∀ f : SDEState d → ℝ, (∃ K, LipschitzWith K f) → Integrable f π →
        H3 P b σ W f π η₀ (1 / 2) c₃) ∧
      H4 P b σ W x₀ η₀ (c1fun b σ α L x₀) c₄ ∧
      max (α * c₂ ^ 2 / L ^ 2) (max (α * c₃ ^ 2 / L ^ 2) (c₄ ^ 2)) ≤
        cu * Upsilon1Sq b σ α x₀ := by sorry

end MLLangevin.ConvexA1
