-- Prove2me | Theorems.Thm_HedgePSNV_hedging_completeness
-- name    : HedgePSNV.hedging_completeness
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T14:41:05.657168+00:00
-- url     : https://prove2.me/theorems/ccbabdc3-d23d-456f-a429-a94bf9dab1a6
-- title:
--   Completeness: a claim orthogonal to constants, admissible gains and weighted $d\tilde B$-sums vanishes
-- statement:
--   Let $f\in L^2(\mathbb P)$ be $\mathcal F_T$-measurable with $\mathbb E f=0$, $\mathbb E[f\,\chi_T]=0$ for every admissible gains process $\chi$, and $\mathbb E\big[f\,Z_T\sum_k Y_k(\tilde B_{t_{k+1}}-\tilde B_{t_k})\big]=0$ for every uniform grid and bounded adapted $Y_k$. Then $$f=0\quad\mathbb P\text{-a.s.}$$
--
--   Role: the density statement behind the upper bound of (21).
-- source:
--   Wang-Yao-Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, https://arxiv.org/abs/2201.01026v4, proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory HedgePSNV
open scoped NNReal ENNReal

namespace HedgePSNV

theorem hedging_completeness (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hXM : IsMartingaleOn p.T M.F M.PM M.X)
    (f : Ω → ℝ) (hfm : StronglyMeasurable[M.F p.T] f) (hf2 : MemLp f 2 M.P)
    (hf1 : ∫ ω, f ω ∂M.P = 0)
    (hfA : ∀ θχ ∈ M.AX, ∫ ω, f ω * θχ.2 p.T ω ∂M.P = 0)
    (hfN : ∀ n : ℕ, 0 < n → ∀ Y : ℕ → Ω → ℝ,
      (∀ k : ℕ, Measurable[M.F ((k : ℝ≥0) * (p.T / n))] (Y k)) → (∃ C : ℝ, ∀ (k : ℕ) ω, |Y k ω| ≤ C) →
      ∫ ω, f ω * (M.Z p.T ω * ∑ k ∈ Finset.range n, Y k ω *
        (M.Bt (((k + 1 : ℕ) : ℝ≥0) * (p.T / n)) ω - M.Bt ((k : ℝ≥0) * (p.T / n)) ω)) ∂M.P = 0) :
    f =ᵐ[M.P] 0 := by sorry

end HedgePSNV
