-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_proposition_2_1
-- name    : GPhNGIDiffusion.EMError.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:52.612859+00:00
-- url     : https://prove2.me/theorems/20ca9fe4-a00c-4cdd-9895-47cecdaef8be
-- title:
--   Proposition 2.1: unique $\tilde\mu_\eta$, $d_W,\|\cdot\|_{\mathrm{TV}}((\tilde P^k_\eta)^*\nu,\tilde\mu_\eta)\le C\eta^{-1}e^{-ck\eta}$, $\tilde\mu_\eta(|\cdot|^\ell)\le C$
-- statement:
--   Consider the Euler–Maruyama chain (1.2) of a model. There is $\eta_0>0$ such that:
--
--   1. for every step $\eta\in(0,\eta_0]$ the chain has a unique invariant probability measure $\tilde\mu_\eta$;
--   2. for every probability measure $\nu$ with $\nu(|\cdot|^2)<\infty$ there are constants $C,c>0$, independent of $k$ and $\eta$, such that for all $\eta\in(0,\eta_0]$ and all $k\in\mathbb N_0$,
--   $$
--   d_W\big((\tilde P^k_\eta)^*\nu,\tilde\mu_\eta\big)\le C\eta^{-1}e^{-ck\eta},\qquad
--   \big\|(\tilde P^k_\eta)^*\nu-\tilde\mu_\eta\big\|_{\mathrm{TV}}\le C\eta^{-1}e^{-ck\eta};
--   $$
--   3. for every integer $\ell\ge2$ there is a constant $C$, depending on $\ell$ but not on $\eta$, with $\tilde\mu_\eta(|\cdot|^\ell)\le C$ for all $\eta\in(0,\eta_0]$.
--
--   Existence, uniqueness and the uniform moment bounds of $\tilde\mu_\eta$ are what the proof of Theorem 1.2 needs from the chain; the exponential ergodicity is the second half of the first sentence of Theorem 1.2.
--
--   **Formalization Note** The threshold $\eta_0$ is explicit in the proof ("for small enough $\eta>0$", p. 25) and implicit in the statement. The measure $\nu$ is a probability measure (its image $(\tilde P^k_\eta)^*\nu$ is compared in $d_W$ with a probability measure). The constants are stated after $\nu$, as in the paper, and before $\eta$ and $k$, as "independent of $k$ and $\eta$" requires. Moments are lower Lebesgue integrals.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 9, Proposition 2.1; proof pp. 25-26

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

/-- Proposition 2.1, p. 9: there is `η₀ > 0` such that for every step `η ∈ (0, η₀]` the
Euler–Maruyama chain (1.2) has a unique invariant probability measure `µ̃_η`; it is exponentially
ergodic: for every probability measure `ν` with `ν(|·|²) < ∞` there are `C, c > 0`, independent of
`k` and `η`, with `d_W((P̃^k_η)^*ν, µ̃_η) ≤ Cη^{−1}e^{−ckη}` and
`‖(P̃^k_η)^*ν − µ̃_η‖_TV ≤ Cη^{−1}e^{−ckη}` for all `k ∈ ℕ₀`; and for every integer `ℓ ≥ 2` there is
`C`, not depending on `η`, with `µ̃_η(|·|^ℓ) ≤ C`. -/
theorem proposition_2_1 {d : ℕ} (M : Model d) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      (∀ η : ℝ, 0 < η → η ≤ η₀ → ∃! μt : Measure (EthierKurtz.SDEState d),
        IsEMInvariant M.drift M.σ η μt) ∧
      (∀ ν : Measure (EthierKurtz.SDEState d), IsProbabilityMeasure ν →
        ∫⁻ x, ‖x‖ₑ ^ 2 ∂ν < ∞ →
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ μt : Measure (EthierKurtz.SDEState d),
            IsEMInvariant M.drift M.σ η μt → ∀ k : ℕ,
              dW (emLaw M.drift M.σ η ν k) μt ≤
                  ENNReal.ofReal (C * η⁻¹ * Real.exp (-c * k * η)) ∧
              tvNorm (emLaw M.drift M.σ η ν k) μt ≤
                  ENNReal.ofReal (C * η⁻¹ * Real.exp (-c * k * η))) ∧
      (∀ ℓ : ℕ, 2 ≤ ℓ → ∃ C : ℝ, ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ μt : Measure (EthierKurtz.SDEState d), IsEMInvariant M.drift M.σ η μt →
          ∫⁻ x, ‖x‖ₑ ^ ℓ ∂μt ≤ ENNReal.ofReal C) := by sorry

end GPhNGIDiffusion.EMError
