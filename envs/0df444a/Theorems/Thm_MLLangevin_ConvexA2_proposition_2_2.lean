-- Prove2me | Theorems.Thm_MLLangevin_ConvexA2_proposition_2_2
-- name    : MLLangevin.ConvexA2.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:20.811345+00:00
-- url     : https://prove2.me/theorems/f7d3ca77-233e-4163-85a7-25836d15a0ac
-- title:
--   Proposition 2.2, p. 11 — (H₂), (H₃), (H₄) hold for 𝔞 = 2, δ = 1 with max(α²c₂²/L⁴, α²c₃²/L⁴, c₄²) ≲_uc Υ₂²
-- statement:
--   There is a universal constant $\mathfrak c_u$ such that the following holds. Assume $(\mathbf C_\alpha)$ with $\alpha\in(0,L\wedge1]$, that $b$ is $L$-Lipschitz and $\mathcal C^2$ with bounded partial derivatives up to order 2, and $\sigma>0$. Let $B^{(0)},B^{(1)},\dots$ be standard $d$-dimensional Brownian motions, $X^x$ the solution of $X^x_t=x+\int_0^tb(X^x_s)ds+\sigma B^{(0)}_t$ for each $x$, and $\pi$ a probability measure invariant for this diffusion. Let $x_0\in\mathbb R^d$ and $\gamma\in(0,\frac{\alpha}{2L^2}\wedge\frac12]$. Then there are constants $c_2,c_3,c_4$ such that, with $\eta_0=\gamma$:
--
--   1. $(\mathbf H_2)$ holds with $\mathfrak a=2$ and $c_2$;
--   2. for every Lipschitz $f$ integrable for $\pi$, $(\mathbf H_3)$ holds with $\delta=1$ and $c_3$;
--   3. $(\mathbf H_4)$ holds with $c_4$ and $c_1(x)=|x-x_0|+\sqrt{|b(x_0)|^2(L^{-2}+2\alpha^{-2})+2\sigma^2d/\alpha}$;
--   4. $\displaystyle\max\Big(\frac{\alpha^2c_2^2}{L^4},\frac{\alpha^2c_3^2}{L^4},c_4^2\Big)\le\mathfrak c_u\Upsilon_2^2$, where
--   $$\Upsilon_2^2=\max\Big(1,\ \frac{1}{\alpha^2}|b(x_0)|^2+\frac{\sigma\sqrt\alpha}{L^3}\|\nabla b\|_{2,\infty}|b(x_0)|+\frac{\sigma^4}{L^4}\|\Delta b\|^2_{2,\infty}+\frac{\sigma^2\alpha d^{1/2}}{L^3}\|\nabla b\|_{2,\infty}+\frac{\sigma^2d}{\alpha}\Big). \tag{19}$$
--
--   This verifies the hypotheses of the general complexity theorem in the second-order regime, with all constants controlled by the single quantity $\Upsilon_2$.
--
--   **Formalization Note** The page writes "suppose $\gamma\in(0,\frac{\alpha}{2L^2}\wedge\frac12]$"; this $\gamma$ is the $\eta_0$ of $(\mathbf H_2)$–$(\mathbf H_4)$. The range $\alpha\le L\wedge1$ is the standing range of §2.4 (Proposition 2.1, Theorem 2.3); $\alpha\le1$ is needed for the bound on the $d^{1/2}\|\nabla b\|_{2,\infty}$ term. The $c_1$ of $(\mathbf H_4)$ is the one of Lemma 5.1 with $x^\star=x_0$ ("the results for $(\mathbf H_1)$ and $(\mathbf H_4)$ ... still hold", p. 11). $c_2,c_3,c_4$ depend on the data; $\mathfrak c_u$ does not.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Proposition 2.2 and (19), p. 11; proof, §5.2, p. 36

import Mathlib
import Definitions.Def_MLLangevin_ConvexA2_Multilevel
import Definitions.Def_MLLangevin_ConvexA2_DriftNorms

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

theorem proposition_2_2 :
    ∃ cu : ℝ, ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℕ → ℝ≥0 → Ω → SDEState d), (∀ r, IsStandardBrownian P (B r)) →
      ∀ (b : SDEState d → SDEState d) (L α σ : ℝ),
      (∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖) → MLLangevin.ConvexA1.CondC b α → 0 < α → α ≤ min L 1 → C2Bounded b →
      0 < σ →
      ∀ (Xsol : SDEState d → ℝ≥0 → Ω → SDEState d), (∀ x, IsAddSolution b σ (B 0) x (Xsol x)) →
      ∀ (π : Measure (SDEState d)), IsProbabilityMeasure π → IsInvDiffusion P Xsol π →
      ∀ (x₀ : SDEState d) (γ : ℝ), 0 < γ → γ ≤ min (α / (2 * L ^ 2)) (1 / 2) →
        ∃ c₂ c₃ c₄ : ℝ, H2 P b σ B x₀ γ 2 c₂ ∧
          (∀ f : SDEState d → ℝ, (∃ K, LipschitzWith K f) → Integrable f π →
            H3 b σ f π γ 1 c₃) ∧
          H4 P b σ B x₀ γ (MLLangevin.ConvexA1.c1fun b σ α L x₀) c₄ ∧
          max (α ^ 2 * c₂ ^ 2 / L ^ 4) (max (α ^ 2 * c₃ ^ 2 / L ^ 4) (c₄ ^ 2))
            ≤ cu * Upsilon2Sq b σ α L x₀ := by sorry

end MLLangevin.ConvexA2
