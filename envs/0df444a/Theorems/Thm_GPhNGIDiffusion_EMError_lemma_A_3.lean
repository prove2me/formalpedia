-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_lemma_A_3
-- name    : GPhNGIDiffusion.EMError.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:35.586844+00:00
-- url     : https://prove2.me/theorems/98a7cffa-5423-4ebb-aa5d-8f3dd442b28d
-- title:
--   Lemma A.3: $\mathbb E|X^x_s-x|^{2\ell}\le\tilde C_\ell(1+V^\ell(x))s^\ell$ and $\mathbb E|X^x_\eta-\tilde X^{\eta,x}_1|^{2\ell}\le\tilde C_\ell(1+V^\ell(x))\eta^{3\ell}$
-- statement:
--   Let $V$ be a Lyapunov function of a model with constants $c_1,\breve c_1$. For every integer $\ell\ge1$ there is a constant $\tilde C_\ell>0$, depending on $\ell$ but not on $\eta$, with the following property. Let $(B_t)_{t\ge0}$ be a standard $d$-dimensional Brownian motion, $(X^x_t)_{t\ge0}$ the solution of (1.1) started at $x$ and driven by $B$, and
--   $$
--   \tilde X^{\eta,x}_1=x+g(x)\eta+\sigma(B_\eta-B_0)
--   $$
--   the first Euler–Maruyama step driven by the same Brownian increment, as in (A.9). Then for $0\le s<1$ and $0\le\eta<1$,
--   $$
--   \mathbb E|X^x_s-x|^{2\ell}\le\tilde C_\ell(1+V^\ell(x))s^\ell,\qquad
--   \mathbb E|X^x_\eta-\tilde X^{\eta,x}_1|^{2\ell}\le\tilde C_\ell(1+V^\ell(x))\eta^{3\ell}.
--   $$
--
--   The second bound is the one-step local error of the Euler–Maruyama scheme; it is the input to the drift condition for the chain in Lemma A.4.
--
--   **Formalization Note** The coupling (A.9) of the chain with the diffusion through the same Brownian motion is explicit. Expectations are lower Lebesgue integrals. The step $\eta$ is restricted to $[0,1)$, the range $0\le s<1$ of the lemma at $s=\eta$, which is how the paper uses it. The statement holds for every Lyapunov function with properties (A.5)–(A.7).
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 24, Lemma A.3, (A.9); proof pp. 27-28

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

/-- Lemma A.3, p. 24: for every integer `ℓ ≥ 1` there is `C̃_ℓ > 0`, not depending on `η`, such that
for every solution `X^x` of (1.1) driven by a standard Brownian motion `B`, and the Euler–Maruyama step
driven by the same increment, `X̃^{η,x}_1 = x + g(x)η + σ(B_η − B_0)` ((A.9)),
`E|X^x_s − x|^{2ℓ} ≤ C̃_ℓ(1 + V^ℓ(x))s^ℓ` for `0 ≤ s < 1`, and
`E|X^x_η − X̃^{η,x}_1|^{2ℓ} ≤ C̃_ℓ(1 + V^ℓ(x))η^{3ℓ}` for `0 ≤ η < 1`. -/
theorem lemma_A_3 {d : ℕ} (M : Model d)
    (V : EthierKurtz.SDEState d → ℝ) (c₁ c₁' : ℝ) (hV : IsLyapunovFn M V c₁ c₁')
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
        (B X : ℝ≥0 → Ω → EthierKurtz.SDEState d) (x : EthierKurtz.SDEState d),
        EthierKurtz.IsStandardBrownian Pr B → SolvesAdditiveSDE M.drift M.σ B X x →
        (∀ s : ℝ≥0, s < 1 →
          ∫⁻ ω, ‖X s ω - x‖ₑ ^ (2 * ℓ) ∂Pr ≤
            ENNReal.ofReal (Ct * (1 + V x ^ ℓ) * (s : ℝ) ^ ℓ)) ∧
        (∀ η : ℝ≥0, η < 1 →
          ∫⁻ ω, ‖X η ω - (x + (η : ℝ) • M.drift x + mv M.σ (B η ω - B 0 ω))‖ₑ ^ (2 * ℓ) ∂Pr ≤
            ENNReal.ofReal (Ct * (1 + V x ^ ℓ) * (η : ℝ) ^ (3 * ℓ))) := by sorry

end GPhNGIDiffusion.EMError
