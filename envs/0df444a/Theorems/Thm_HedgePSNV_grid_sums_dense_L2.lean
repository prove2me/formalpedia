-- Prove2me | Theorems.Thm_HedgePSNV_grid_sums_dense_L2
-- name    : HedgePSNV.grid_sums_dense_L2
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:02:23.608175+00:00
-- url     : https://prove2.me/theorems/241708a8-a5f6-47c1-bca4-9cd9d3fbcaaf
-- title:
--   Uniform-grid simple $dB$ and $d\tilde B$ sums are dense in $L^2(\mathcal F_T)$
-- statement:
--   If $V\in L^2(\mathcal F_T)$ is orthogonal to every $c+\sum_k Y_k\Delta_kB+\sum_k Z_k\Delta_k\tilde B$ on a uniform grid with bounded adapted $Y_k,Z_k$, then $$V=0\quad\text{a.s.}$$
--
--   Role: a step of the completeness argument (every square-integrable claim orthogonal to all hedgeable gains vanishes).
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Section 3.4, Lemma 4.2 and Proposition 4.14 (density of simple integrals; martingale representation); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

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

theorem grid_sums_dense_L2 {p : HedgePSNV.Params} {Ω : Type*} [MeasurableSpace Ω] (M : HedgePSNV.Model p Ω)
    (hM : M.Standing) (V : Ω → ℝ)
    (hV : MemLp V 2 (M.P.trim (M.F.le p.T)))
    (horth : ∀ f : Ω → ℝ, (∃ n : ℕ, 0 < n ∧ ∃ c : ℝ, ∃ Y Z : ℕ → Ω → ℝ, ∃ C : ℝ,
      (∀ k : ℕ, StronglyMeasurable[M.F ((k : ℝ≥0) * (p.T / (n : ℝ≥0)))] (Y k)) ∧ (∀ k ω, |Y k ω| ≤ C) ∧
      (∀ k : ℕ, StronglyMeasurable[M.F ((k : ℝ≥0) * (p.T / (n : ℝ≥0)))] (Z k)) ∧ (∀ k ω, |Z k ω| ≤ C) ∧
      f = fun ω => c +
        ∑ k ∈ Finset.range n, Y k ω * (M.B (((k + 1 : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0))) ω -
          M.B ((k : ℝ≥0) * (p.T / (n : ℝ≥0))) ω) +
        ∑ k ∈ Finset.range n, Z k ω * (M.Bt (((k + 1 : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0))) ω -
          M.Bt ((k : ℝ≥0) * (p.T / (n : ℝ≥0))) ω)) →
      ∫ ω, V ω * f ω ∂(M.P.trim (M.F.le p.T)) = 0) :
    V =ᵐ[M.P.trim (M.F.le p.T)] 0 := by sorry

end HedgePSNV
