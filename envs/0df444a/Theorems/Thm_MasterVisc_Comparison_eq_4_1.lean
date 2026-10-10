-- Prove2me | Theorems.Thm_MasterVisc_Comparison_eq_4_1
-- name    : MasterVisc.Comparison.eq_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:35.877748+00:00
-- url     : https://prove2.me/theorems/5a931c25-af78-41c0-9a48-16e4bda08a79
-- title:
--   (4.1), p. 958 — sup over 𝒫_L(t, μ) of 𝔼[sup_{t≤s≤t+δ} |X_{t,s}|^p] ≤ C_{p,L} δ^{p/2}
-- statement:
--   Let $p\ge1$ and $L>0$. There is a constant $C_{p,L}$ (depending on $p$, $L$, $d$ and $T$ only) such that for every $(t,\mu)\in\Theta$ and every $\delta\in[0,T-t]$,
--   $$\sup_{\mathbb P\in\mathcal P_L(t,\mu)}\mathbb E^{\mathbb P}\Big[\sup_{t\le s\le t+\delta}|X_{t,s}|^p\Big]\le C_{p,L}\,\delta^{p/2}.$$
--   Here $\mathcal P_L(t,\mu)$ is the set of laws that agree with $\mu$ up to time $t$ and are semimartingales on $[t,T]$ with drift and diffusion characteristics bounded by $L$, and $X_{t,s}=X_s-X_t$.
--
--   This moment estimate is used throughout §4 (compactness of $\mathcal P_L(t,\mu)$, Lemma 4.1) and in §5.
--
--   **Formalization Note.** The expectation is a lower Lebesgue integral of the extended-valued supremum, so no integrability hypothesis is needed. The constant is quantified before $t$, $\mu$, $\delta$ and $\mathbb P$.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), (4.1), §4.1, p. 958

import Mathlib
import Definitions.Def_MasterVisc_Comparison_Setting
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace MasterVisc.Comparison

/-- (4.1), p. 958: for `p ≥ 1` and `L > 0` there is `C_{p,L}` such that for all `(t, μ) ∈ Θ`,
`δ ∈ [0, T − t]` and `ℙ ∈ 𝒫_L(t, μ)`, `𝔼^ℙ[sup_{t ≤ s ≤ t+δ} |X_{t,s}|^p] ≤ C_{p,L} δ^{p/2}`. -/
theorem eq_4_1 {d : ℕ} {T : ℝ≥0} (p : ℝ) (hp : 1 ≤ p) (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, ∀ (t δ : ℝ≥0) (μ : Measure (Path d T)), t ≤ T → IsP2 μ → δ ≤ T - t →
      ∀ P : Measure (Path d T), InPL L t μ P →
        ∫⁻ ω, (⨆ s ∈ Set.Icc t (t + δ), ‖evalAt s ω - evalAt t ω‖ₑ) ^ p ∂P ≤
          ENNReal.ofReal (C * (δ : ℝ) ^ (p / 2)) := by sorry

end MasterVisc.Comparison
