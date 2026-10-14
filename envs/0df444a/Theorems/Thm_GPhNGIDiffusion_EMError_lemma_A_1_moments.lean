-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_lemma_A_1_moments
-- name    : GPhNGIDiffusion.EMError.lemma_A_1_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:34.088073+00:00
-- url     : https://prove2.me/theorems/634f27e7-1095-4e0f-9282-f88f5d22cc0c
-- title:
--   Lemma A.1 (moments): $\mathcal AV^\ell\le -c_1V^\ell+\breve c_\ell$, $\mathbb EV^\ell(X^x_t)\le e^{-c_1t}V^\ell(x)+\breve c_\ell(1-e^{-c_1t})/c_1$, $\mu(V^\ell)\le\breve c_\ell/c_1$
-- statement:
--   Let $(P_t)_{t\ge0}$ be the transition function of the limiting diffusion (1.1) of a model, $\mu$ an invariant probability measure, and $V$ a Lyapunov function of the model with constants $c_1,\breve c_1$ (properties (A.5)–(A.7)). For every integer $\ell\ge1$ there is a constant $\breve c_\ell>0$ such that
--   $$
--   \mathcal AV^\ell(x)\le -c_1V^\ell(x)+\breve c_\ell\qquad\text{for all }x,
--   $$
--   $$
--   \mathbb E\,V^\ell(X^x_t)\le e^{-c_1t}V^\ell(x)+\frac{\breve c_\ell(1-e^{-c_1t})}{c_1}\qquad\text{for all }x\text{ and } t\ge0, \tag{A.8}
--   $$
--   and $\mu(V^\ell)\le \breve c_\ell/c_1$. Moreover $\mu(|\cdot|^{2\ell})\le C$ for a constant $C$ depending on $\ell$.
--
--   These moment bounds give uniform-in-time control of the diffusion and show that $\mu$ has moments of all orders, so that $d_W$ distances to $\mu$ are finite.
--
--   **Formalization Note** This is the first half of Lemma A.1; its exponential ergodicity is the separate item `lemma_A_1_ergodicity`. The statement holds for every Lyapunov function with properties (A.5)–(A.7), which is all the paper's proof uses of the specific $V$ of (A.4). $\mathbb E\,V^\ell(X^x_t)$ is $\int V^\ell\,dP_t(x,\cdot)$, and all expectations of nonnegative functions are lower Lebesgue integrals, so no bound can hold because an integral defaults to $0$.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 24, Lemma A.1 (first part, (A.8)); proof pp. 26-27

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

/-- Lemma A.1, first part, p. 24: for every integer `ℓ ≥ 1` there is `c̆_ℓ > 0` with
`AV^ℓ ≤ −c₁V^ℓ + c̆_ℓ`, the moment bound (A.8)
`E V^ℓ(X^x_t) ≤ e^{−c₁t}V^ℓ(x) + c̆_ℓ(1 − e^{−c₁t})/c₁` for all `t ≥ 0`, `µ(V^ℓ) ≤ c̆_ℓ/c₁`, and
`µ(|·|^{2ℓ}) ≤ C` for a constant `C` depending on `ℓ`. -/
theorem lemma_A_1_moments {d : ℕ} (M : Model d)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hP : IsTransitionFunction M.drift M.σ P)
    (μ : Measure (EthierKurtz.SDEState d)) (hμ : IsInvariantMeasure P μ)
    (V : EthierKurtz.SDEState d → ℝ) (c₁ c₁' : ℝ) (hV : IsLyapunovFn M V c₁ c₁')
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ cℓ : ℝ, 0 < cℓ ∧
      (∀ x, generator M.drift M.σ (fun y => V y ^ ℓ) x ≤ -c₁ * V x ^ ℓ + cℓ) ∧
      (∀ (x : EthierKurtz.SDEState d) (t : ℝ≥0),
        ∫⁻ y, ENNReal.ofReal (V y ^ ℓ) ∂(P t x) ≤
          ENNReal.ofReal (Real.exp (-c₁ * t) * V x ^ ℓ + cℓ * (1 - Real.exp (-c₁ * t)) / c₁)) ∧
      ∫⁻ y, ENNReal.ofReal (V y ^ ℓ) ∂μ ≤ ENNReal.ofReal (cℓ / c₁) ∧
      ∃ C : ℝ, ∫⁻ y, ‖y‖ₑ ^ (2 * ℓ) ∂μ ≤ ENNReal.ofReal C := by sorry

end GPhNGIDiffusion.EMError
