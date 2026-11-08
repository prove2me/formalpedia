-- Prove2me | Theorems.Thm_HedgePSNV_tilted_orthogonality_vanish
-- name    : HedgePSNV.tilted_orthogonality_vanish
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:19:12.505347+00:00
-- url     : https://prove2.me/theorems/353a1fbc-d263-440e-b5c3-d64b1229325d
-- title:
--   Orthogonality to $\mathcal G_T$ and to tilted $d\tilde B$-increments forces $f=0$
-- statement:
--   Let $Q$ have density $Z_T^2/\mathbb E Z_T^2$. If $f\in L^2$ is $\mathcal F_T$-measurable, $\mathbb E^Q[(f/Z_T)\zeta]=0$ for bounded $\mathcal G_T$-measurable $\zeta$, and $\mathbb E^Q[(f/Z_T)\,y\,(\tilde B_{t_{j+1}}-\tilde B_{t_j})]=0$ for bounded $\mathcal F_{t_j}\vee\mathcal G_T$-measurable $y$, then $$f=0\quad\mathbb P\text{-a.s.}$$
--
--   Role: a step of the completeness argument (every square-integrable claim orthogonal to all hedgeable gains vanishes).
-- source:
--   Wang-Yao-Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, https://arxiv.org/abs/2201.01026v4, Assumption 5 (Markov structure); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped NNReal

namespace HedgePSNV

theorem tilted_orthogonality_vanish {p : HedgePSNV.Params} {Ω : Type*} [MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) {f : Ω → ℝ}
    (hfm : StronglyMeasurable[M.F p.T] f) (hf2 : MemLp f 2 M.P)
    (hG : ∀ ζ : Ω → ℝ, Measurable[M.G p.T] ζ → ∀ C : ℝ, (∀ ω, |ζ ω| ≤ C) →
      ∫ ω, f ω / M.Z p.T ω * ζ ω ∂(M.P.withDensity fun ω => ENNReal.ofReal (M.Z p.T ω ^ 2 / ∫ ω', M.Z p.T ω' ^ 2 ∂M.P)) = 0)
    (hE : ∀ N j : ℕ, j < N → ∀ y : Ω → ℝ, Measurable[M.F (((j : ℕ) : ℝ≥0) * (p.T / (N : ℝ≥0))) ⊔ M.G p.T] y →
      ∀ Cy : ℝ≥0, (∀ ω, |y ω| ≤ Cy) →
      ∫ ω, f ω / M.Z p.T ω * y ω * (M.Bt (((j + 1 : ℕ) : ℝ≥0) * (p.T / (N : ℝ≥0))) ω - M.Bt (((j : ℕ) : ℝ≥0) * (p.T / (N : ℝ≥0))) ω) ∂(M.P.withDensity fun ω => ENNReal.ofReal (M.Z p.T ω ^ 2 / ∫ ω', M.Z p.T ω' ^ 2 ∂M.P)) = 0) :
    f =ᵐ[M.P] 0 := by sorry

end HedgePSNV
