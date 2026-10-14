-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_claims_2_7_2_8
-- name    : GPhNGIDiffusion.EMError.claims_2_7_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:47.52805+00:00
-- url     : https://prove2.me/theorems/097106aa-df4e-4757-9ce2-9bb3d20ebf87
-- title:
--   Claims (2.7)–(2.8): the Stein Taylor remainder is $\le C_\varsigma\eta^{(3-\varsigma)/2}$ on $\{|\delta|<1\}$ and $\le C\eta^{3/2}$ on $\{|\delta|\ge1\}$
-- statement:
--   Let $(P_t)$ be the transition function and $\mu$ an invariant probability measure of the limiting diffusion (1.1) of a model. For a step $\eta$, let $\tilde\mu_\eta$ be an invariant probability measure of the Euler–Maruyama chain, let $W\sim\tilde\mu_\eta$ and $\xi_1$ be an independent standard Gaussian vector, $W'=W+g(W)\eta+\sqrt\eta\,\sigma\xi_1$ and $\delta=W'-W$. For $h\in\mathrm{Lip}_0(1)$ let $f$ be the Stein solution of $\mathcal Af=h-\mu(h)$ and
--   $$
--   J=\int_0^1\!\!\int_0^1 r\,\big\langle\delta\delta',\ \nabla^2f(W+\tilde rr\delta)-\nabla^2f(W)\big\rangle_{\mathrm{HS}}\,d\tilde r\,dr .
--   $$
--   There is $\eta_0\in(0,1)$ such that:
--
--   1. for every $\varsigma\in(0,1)$ there is $C_\varsigma>0$, not depending on $\eta$ or $h$, with
--   $$
--   \mathbb E\,\big|J\,1_{\{|\delta|<1\}}\big|\le C_\varsigma\,\eta^{\frac{3-\varsigma}2}\qquad\text{for all }\eta\in(0,\eta_0]; \tag{2.7}
--   $$
--   2. there is $C>0$, not depending on $\eta$ or $h$, with
--   $$
--   \mathbb E\,\big|J\,1_{\{|\delta|\ge1\}}\big|\le C\,\eta^{\frac32}\qquad\text{for all }\eta\in(0,\eta_0]. \tag{2.8}
--   $$
--
--   Together they bound the second-order remainder of the Taylor expansion in the Stein argument, which yields $d_W(\mu,\tilde\mu_\eta)\le C_\varsigma\eta^{(1-\varsigma)/2}$.
--
--   **Formalization Note** These are the two claims stated inside the proof of Theorem 1.2. The expectation over $(W,\xi_1)$ is the iterated lower Lebesgue integral against $\tilde\mu_\eta\otimes\mathcal N(0,I)$. The constants are uniform over $h\in\mathrm{Lip}_0(1)$ because the proof takes the supremum over $h$; "small $\eta<1$" is the threshold $\eta_0<1$.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 10, (2.7)-(2.8); set-up p. 9; proof p. 11

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Model
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_EulerMaruyama
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace GPhNGIDiffusion.EMError

/-- Claims (2.7)–(2.8), p. 10, in the proof of Theorem 1.2. Let `W ∼ µ̃_η` be the stationary initial
value of the Euler–Maruyama chain, `W′ = W + ηg(W) + √η σξ₁` its next value and `δ = W′ − W`; let `f`
be the solution (3.2) of the Stein equation (2.1) for `h ∈ Lip₀(1)`, and
`J = ∫₀¹∫₀¹ r⟨δδ′, ∇²f(W + r̃rδ) − ∇²f(W)⟩_HS dr̃ dr`. There is `η₀ ∈ (0, 1)` such that:
for every `ς ∈ (0, 1)` there is `C_ς > 0`, not depending on `η` (nor on `h`), with
`E|J 1_{|δ|<1}| ≤ C_ς η^{(3−ς)/2}` (2.7), and there is `C > 0`, not depending on `η` (nor on `h`), with
`E|J 1_{|δ|≥1}| ≤ C η^{3/2}` (2.8), for all `η ∈ (0, η₀]`. -/
theorem claims_2_7_2_8 {d : ℕ} (M : Model d)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hP : IsTransitionFunction M.drift M.σ P)
    (μ : Measure (EthierKurtz.SDEState d)) (hμ : IsInvariantMeasure P μ) :
    let δ : ℝ → EthierKurtz.SDEState d → EthierKurtz.SDEState d → EthierKurtz.SDEState d :=
      fun η w z => η • M.drift w + Real.sqrt η • mv M.σ z
    let J : (EthierKurtz.SDEState d → ℝ) → EthierKurtz.SDEState d → EthierKurtz.SDEState d → ℝ :=
      fun h w u => ∫ r in (0 : ℝ)..1, ∫ r' in (0 : ℝ)..1,
        r * ∑ i, ∑ j, u i * u j *
          (partial2 (steinSolution P μ h) i j (w + (r' * r) • u)
            - partial2 (steinSolution P μ h) i j w)
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧
      (∀ ς : ℝ, 0 < ς → ς < 1 → ∃ Cς : ℝ, 0 < Cς ∧
        ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ μt : Measure (EthierKurtz.SDEState d),
          IsEMInvariant M.drift M.σ η μt → ∀ h : EthierKurtz.SDEState d → ℝ, IsLip1Zero h →
            ∫⁻ w, ∫⁻ z, (if ‖δ η w z‖ < 1 then ENNReal.ofReal |J h w (δ η w z)| else 0)
                ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt ≤
              ENNReal.ofReal (Cς * η ^ ((3 - ς) / 2))) ∧
      (∃ C : ℝ, 0 < C ∧
        ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ μt : Measure (EthierKurtz.SDEState d),
          IsEMInvariant M.drift M.σ η μt → ∀ h : EthierKurtz.SDEState d → ℝ, IsLip1Zero h →
            ∫⁻ w, ∫⁻ z, (if 1 ≤ ‖δ η w z‖ then ENNReal.ofReal |J h w (δ η w z)| else 0)
                ∂(stdGaussian (EthierKurtz.SDEState d)) ∂μt ≤
              ENNReal.ofReal (C * η ^ (3 / 2 : ℝ))) := by sorry

end GPhNGIDiffusion.EMError
