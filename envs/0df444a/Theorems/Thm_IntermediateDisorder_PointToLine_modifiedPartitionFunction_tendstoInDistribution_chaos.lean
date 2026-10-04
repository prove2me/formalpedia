-- Prove2me | Theorems.Thm_IntermediateDisorder_PointToLine_modifiedPartitionFunction_tendstoInDistribution_chaos
-- name    : IntermediateDisorder.PointToLine.modifiedPartitionFunction_tendstoInDistribution_chaos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:24:22.358796+00:00
-- url     : https://prove2.me/theorems/ead56ca5-c31e-4ff6-86e8-7ce94802490b
-- title:
--   Proposition 5.3 (Theorem 2.1, first bullet) — $\mathfrak z_n^\omega(\beta n^{-1/4})\to\mathcal Z_{\sqrt2\beta}$ in law
-- statement:
--   Assume that the environment variables $\omega(i,x)$ are i.i.d. with mean zero and variance one, and let $\beta>0$. Let $W$ be a white noise on $[0,1]\times\mathbb R$ with multiple stochastic integrals $I=(I_k)$, and $\mathcal Z_{\sqrt2\beta}$ the Wiener chaos (7). Then, as $n\to\infty$,
--
--   $$\mathfrak z_n^\omega(\beta n^{-1/4})\xrightarrow{(d)}\mathcal Z_{\sqrt2\beta}=1+\sum_{k\ge1}(\sqrt2\beta)^k\int_{\Delta_k}\int_{\mathbb R^k}\prod_{i=1}^kW(t_i,x_i)\,\varrho(t_i-t_{i-1},x_i-x_{i-1})\,dx_i\,dt_i .$$
--
--   This is the first bullet of Theorem 2.1: under the scaling $\beta n^{-1/4}$ the modified partition function has a non-degenerate random limit, a Wiener chaos built from white noise and the heat kernel. Only two moments of the environment are needed.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, p. 7, Theorem 2.1 (first bullet); proved as Proposition 5.3, p. 30

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory Filter

/-- Proposition 5.3 (Theorem 2.1, first bullet): for an i.i.d. environment with mean zero and
variance one and `β > 0`, `𝔷_n^ω(βn^{-1/4}) → 𝒵_{√2β}` in distribution. -/
theorem modifiedPartitionFunction_tendstoInDistribution_chaos {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ}
    (hω : IsStdEnvironment ω Q)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    (W : Set (ℝ × ℝ) → Ω' → ℝ) (I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q')
    (hW : IsWhiteNoise W Q') (hI : IsMultipleIntegral W Q' I) (β : ℝ) (hβ : 0 < β) :
    TendstoInDistribution
      (fun n => modifiedPartitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))))
      atTop (wienerChaos I (Real.sqrt 2 * β)) (fun _ => Q) Q' := by sorry

end IntermediateDisorder.PointToLine
