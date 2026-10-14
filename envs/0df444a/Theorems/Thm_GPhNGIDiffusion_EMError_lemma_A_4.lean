-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_lemma_A_4
-- name    : GPhNGIDiffusion.EMError.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:41.46877+00:00
-- url     : https://prove2.me/theorems/632f6c64-eb05-4694-8325-594d450f04d3
-- title:
--   Lemma A.4: $\tilde P_\eta V^\ell\le\check\gamma_\ell V^\ell+\check K_\ell$ with $\check\gamma_\ell=e^{-c_1\eta}+\tilde C_\ell\eta^{3/2}<1$
-- statement:
--   Let $V$ be a Lyapunov function of a model with constants $c_1,\breve c_1$, let $\ell\ge1$ be an integer, and let $\breve c_\ell>0$ be a constant as in Lemma A.1, i.e. with $\mathcal AV^\ell\le -c_1V^\ell+\breve c_\ell$. There are a constant $\tilde C_\ell>0$, depending on $\ell$ but not on $\eta$, and a threshold $\eta_\ell\in(0,e^{-1})$ such that for every step $\eta\in(0,\eta_\ell]$, with
--   $$
--   \check\gamma_\ell=e^{-c_1\eta}+\tilde C_\ell\eta^{3/2},\qquad \check K_\ell=\frac{\breve c_\ell}{c_1}(1-e^{-c_1\eta})+\tilde C_\ell\eta^{3/2},
--   $$
--   one has $\check\gamma_\ell<1$ and
--   $$
--   \tilde P_\eta V^\ell(x)\le\check\gamma_\ell V^\ell(x)+\check K_\ell\qquad\text{for all }x\in\mathbb R^d.
--   $$
--
--   This geometric drift condition for the Euler–Maruyama chain gives its exponential ergodicity and the uniform-in-$\eta$ moment bounds of $\tilde\mu_\eta$ in Proposition 2.1.
--
--   **Formalization Note** The lemma states $\check\gamma_\ell\in(0,1)$ and $\check K_\ell\in[0,\infty)$; positivity and nonnegativity are automatic, and $\check\gamma_\ell<1$ needs $\eta$ small, which the proof makes explicit ("for small enough $\eta\in(0,e^{-1})$", p. 29). $\tilde P_\eta V^\ell(x)$ is a lower Lebesgue integral.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 24, Lemma A.4; proof pp. 28-29

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

/-- Lemma A.4, pp. 24, 28–29: for every integer `ℓ ≥ 1` and every constant `c̆_ℓ > 0` as in
Lemma A.1 (`AV^ℓ ≤ −c₁V^ℓ + c̆_ℓ`) there are `C̃_ℓ > 0`, not depending on `η`, and a threshold
`η_ℓ ∈ (0, e^{−1})` such that for every `η ∈ (0, η_ℓ]`, with `γ̌_ℓ = e^{−c₁η} + C̃_ℓη^{3/2}` and
`Ǩ_ℓ = (c̆_ℓ/c₁)(1 − e^{−c₁η}) + C̃_ℓη^{3/2}`, one has `γ̌_ℓ < 1` and
`P̃_η V^ℓ(x) ≤ γ̌_ℓ V^ℓ(x) + Ǩ_ℓ` for all `x`. -/
theorem lemma_A_4 {d : ℕ} (M : Model d)
    (V : EthierKurtz.SDEState d → ℝ) (c₁ c₁' : ℝ) (hV : IsLyapunovFn M V c₁ c₁')
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (cℓ : ℝ) (hcℓ : 0 < cℓ)
    (hgen : ∀ x, generator M.drift M.σ (fun y => V y ^ ℓ) x ≤ -c₁ * V x ^ ℓ + cℓ) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∃ ηℓ : ℝ, 0 < ηℓ ∧ ηℓ < Real.exp (-1) ∧
      ∀ η : ℝ, 0 < η → η ≤ ηℓ →
        Real.exp (-c₁ * η) + Ct * η ^ (3 / 2 : ℝ) < 1 ∧
        ∀ x : EthierKurtz.SDEState d,
          ∫⁻ y, ENNReal.ofReal (V y ^ ℓ) ∂(emStep M.drift M.σ η x) ≤
            ENNReal.ofReal ((Real.exp (-c₁ * η) + Ct * η ^ (3 / 2 : ℝ)) * V x ^ ℓ
              + (cℓ / c₁ * (1 - Real.exp (-c₁ * η)) + Ct * η ^ (3 / 2 : ℝ))) := by sorry

end GPhNGIDiffusion.EMError
