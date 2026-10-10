-- Prove2me | Theorems.Thm_MasterVisc_MKV_eq_4_1
-- name    : MasterVisc.MKV.eq_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:33:40.483469+00:00
-- url     : https://prove2.me/theorems/f92391c9-050e-4667-b444-2f99fbea3328
-- title:
--   (4.1), p. 958 — uniform moment estimate: sup over 𝒫_L(t, μ) of 𝔼[sup_{t≤s≤t+δ} |X_{t,s}|^p] ≤ C_{p,L} δ^{p/2}
-- statement:
--   Let $p\ge1$ and $L>0$. There is a constant $C_{p,L}$ (depending also on the fixed $d$ and $T$) such that for every $(t,\mu)\in\Theta$ and every $\delta\in[0,T-t]$,
--   $$\sup_{\mathbb P\in\mathcal P_L(t,\mu)}\mathbb E^{\mathbb P}\Big[\sup_{t\le s\le t+\delta}|X_{t,s}|^p\Big]\le C_{p,L}\,\delta^{p/2},$$
--   where $X_{t,s}=X_s-X_t$ and $\mathcal P_L(t,\mu)$ is the set of laws in $\mathcal P_2$ agreeing with $\mu$ on $[0,t]$ under which $X$ is a semimartingale on $[t,T]$ with drift and diffusion characteristics bounded by $L$.
--
--   This estimate is used throughout the paper; in this mission it gives the uniform bound of Remark 5.4(i) and the time-continuity estimates in the proof of Theorem 5.8.
--
--   **Formalization Note.** The expectation is a lower Lebesgue integral of the extended nonnegative supremum, so no integrability side condition is needed. The constant is chosen before $(t,\mu,\delta,\mathbb P)$.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), (4.1), §4.1, p. 958

import Mathlib
import Definitions.Def_MasterVisc_MKV_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.MKV

/-- (4.1), p. 958: for `p ≥ 1` and `L > 0` there is `C_{p,L}` with
`sup_{P ∈ 𝒫_L(t,μ)} 𝔼^P[sup_{t ≤ s ≤ t+δ} |X_{t,s}|^p] ≤ C_{p,L} δ^{p/2}` for all `(t, μ) ∈ Θ`,
`δ ∈ [0, T − t]`. -/
theorem eq_4_1 {d : ℕ} {T : ℝ≥0} :
    ∀ p : ℝ, 1 ≤ p → ∀ L : ℝ, 0 < L → ∃ Cp : ℝ, ∀ (t : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T)) (δ : ℝ≥0),
      t ≤ T → MasterVisc.Comparison.IsP2 μ → δ ≤ T - t → ∀ P, InPL L t μ P →
        ∫⁻ ω, (⨆ s ∈ Set.Icc t (t + δ), ‖MasterVisc.Comparison.evalAt s ω - MasterVisc.Comparison.evalAt t ω‖ₑ) ^ p ∂P ≤
          ENNReal.ofReal (Cp * (δ : ℝ) ^ (p / 2)) := by sorry

end MasterVisc.MKV
