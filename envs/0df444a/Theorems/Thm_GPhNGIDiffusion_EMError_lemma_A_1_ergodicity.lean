-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_lemma_A_1_ergodicity
-- name    : GPhNGIDiffusion.EMError.lemma_A_1_ergodicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:34.618771+00:00
-- url     : https://prove2.me/theorems/e43c364d-44b5-49e5-bbba-4751e1959725
-- title:
--   Lemma A.1 (ergodicity): $d_W(P^*_t\nu,\mu)\le C(1+\nu(V))e^{-ct}$, $\|P^*_t\nu-\mu\|_{\mathrm{TV}}\le\|P^*_t\nu-\mu\|_{\mathrm{TV},V^\ell}\le C(1+\nu(V^\ell))e^{-ct}$
-- statement:
--   Let $(P_t)_{t\ge0}$ be the transition function of the limiting diffusion (1.1) of a model, $\mu$ an invariant probability measure, and $V$ a Lyapunov function of the model with constants $c_1,\breve c_1$. For every integer $\ell\ge1$ there are constants $C,c>0$, independent of $t$, such that for every probability measure $\nu$ with $\nu(V^\ell)<\infty$ and every $t\ge0$,
--   $$
--   d_W(P_t^*\nu,\mu)\le C\,(1+\nu(V))\,e^{-ct},
--   $$
--   $$
--   \|P_t^*\nu-\mu\|_{\mathrm{TV}}\le\|P_t^*\nu-\mu\|_{\mathrm{TV},V^\ell}\le C\,(1+\nu(V^\ell))\,e^{-ct}.
--   $$
--
--   This is the exponential ergodicity of the diffusion in the Wasserstein-1, total variation and weighted total variation distances; it identifies $\mu$ as the unique invariant measure and makes the Stein solution $f=-\int_0^\infty(P_th-\mu(h))\,dt$ well defined.
--
--   **Formalization Note** This is the second half of Lemma A.1. The paper says the constants are "independent of $t$" and introduces them after $\nu$; they are stated here before $\nu$ (uniform in $\nu$), which is how the paper uses them (e.g. with $\nu=\delta_x$ uniformly in $x$ in (B.1)). The statement holds for every Lyapunov function with properties (A.5)–(A.7).
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 24, Lemma A.1 (second part); proof p. 27

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

/-- Lemma A.1, second part, p. 24: for every integer `ℓ ≥ 1` there are constants `C, c > 0`,
independent of `t`, such that for every probability measure `ν` with `ν(V^ℓ) < ∞` and every `t ≥ 0`,
`d_W(P*_t ν, µ) ≤ C(1 + ν(V))e^{−ct}` and
`‖P*_t ν − µ‖_TV ≤ ‖P*_t ν − µ‖_{TV,V^ℓ} ≤ C(1 + ν(V^ℓ))e^{−ct}`. -/
theorem lemma_A_1_ergodicity {d : ℕ} (M : Model d)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hP : IsTransitionFunction M.drift M.σ P)
    (μ : Measure (EthierKurtz.SDEState d)) (hμ : IsInvariantMeasure P μ)
    (V : EthierKurtz.SDEState d → ℝ) (c₁ c₁' : ℝ) (hV : IsLyapunovFn M V c₁ c₁')
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ ν : Measure (EthierKurtz.SDEState d), IsProbabilityMeasure ν →
        ∫⁻ y, ENNReal.ofReal (V y ^ ℓ) ∂ν < ∞ → ∀ t : ℝ≥0,
          dW (dualAction P t ν) μ ≤
              ENNReal.ofReal (C * (1 + ∫ y, V y ∂ν) * Real.exp (-c * t)) ∧
          tvNorm (dualAction P t ν) μ ≤
              tvNormWeighted (fun y => V y ^ ℓ) (dualAction P t ν) μ ∧
          tvNormWeighted (fun y => V y ^ ℓ) (dualAction P t ν) μ ≤
              ENNReal.ofReal (C * (1 + ∫ y, V y ^ ℓ ∂ν) * Real.exp (-c * t)) := by sorry

end GPhNGIDiffusion.EMError
