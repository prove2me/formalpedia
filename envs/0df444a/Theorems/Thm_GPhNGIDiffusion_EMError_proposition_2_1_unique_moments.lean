-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_proposition_2_1_unique_moments
-- name    : GPhNGIDiffusion.EMError.proposition_2_1_unique_moments
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T17:55:02.98521+00:00
-- url     : https://prove2.me/theorems/2e93f4c8-c204-40fa-9995-d68900a1cdf0
-- title:
--   Proposition 2.1 (existence, uniqueness and moments of $\tilde\mu_\eta$)
-- statement:
--   Let $(\tilde X^\eta_k)_{k\in\mathbb N_0}$ be the Euler–Maruyama chain (1.2)
--   $$\tilde X^\eta_{k+1}=\tilde X^\eta_k+g(\tilde X^\eta_k)\eta+\sqrt\eta\,\sigma\xi_{k+1}$$
--   of the limiting diffusion of the $G/Ph/n+GI$ queue, with transition kernel $\tilde P_\eta(x,\cdot)=N(x+\eta g(x),\eta\sigma\sigma')$. There is $\eta_0>0$ such that:
--
--   1. for every $\eta\in(0,\eta_0]$ the chain admits a unique invariant probability measure $\tilde\mu_\eta$;
--   2. for every integer $\ell\ge2$ there are $\eta_\ell>0$ and a constant $C$, depending on $\ell$ but not on $\eta$, such that for every $\eta\in(0,\eta_\ell]$ every invariant probability measure $\tilde\mu_\eta$ of the chain with step $\eta$ satisfies
--   $$\tilde\mu_\eta(|\cdot|^\ell)\le C.$$
--
--   **Formalization Note** This is Proposition 2.1 without its exponential-ergodicity display. The milestone `proposition_2_1` additionally asserts $d_W$ and total-variation bounds $C\eta^{-1}e^{-ck\eta}$ with $C,c$ independent of $\eta$; the paper derives those from Tuominen–Tweedie [55] / Douc et al. [20], which give only $\lim_n r(n)\|\tilde P^n_\eta(x,\cdot)-\tilde\mu_\eta\|_\Psi=0$ and whose minorization constant on the petite set degenerates as $\eta\to0$, so the uniformity in $\eta$ is not established there. The downstream proofs of Theorem 1.2(i) and Claims (2.7)–(2.8) use only the two parts stated here. The paper's moment bound holds "for small $\eta$"; the threshold $\eta_\ell$ comes from Lemma A.4 applied to $V^\ell$ and may depend on $\ell$.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 9, Proposition 2.1 (first sentence: existence and uniqueness of $\tilde\mu_\eta$; last display: $\tilde\mu_\eta(|\cdot|^\ell)\le C$); proof pp. 25-26

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

/-- Proposition 2.1 (existence, uniqueness and moments), p. 9: there is `η₀ > 0` such that for
every step `η ∈ (0, η₀]` the Euler–Maruyama chain (1.2) has a unique invariant probability measure
`µ̃_η`; and for every integer `ℓ ≥ 2` there are `η_ℓ > 0` and `C`, not depending on `η`, with
`µ̃_η(|·|^ℓ) ≤ C` for every invariant probability measure `µ̃_η` with step `η ∈ (0, η_ℓ]`. -/
theorem proposition_2_1_unique_moments {d : ℕ} (M : Model d) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      (∀ η : ℝ, 0 < η → η ≤ η₀ → ∃! μt : Measure (EthierKurtz.SDEState d),
        IsEMInvariant M.drift M.σ η μt) ∧
      (∀ ℓ : ℕ, 2 ≤ ℓ → ∃ ηℓ : ℝ, 0 < ηℓ ∧ ∃ C : ℝ, ∀ η : ℝ, 0 < η → η ≤ ηℓ →
        ∀ μt : Measure (EthierKurtz.SDEState d), IsEMInvariant M.drift M.σ η μt →
          ∫⁻ x, ‖x‖ₑ ^ ℓ ∂μt ≤ ENNReal.ofReal C) := by sorry

end GPhNGIDiffusion.EMError
