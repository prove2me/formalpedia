-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_fact_3
-- name    : LargeSupplyFPA.Asymptotic.fact_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:03:42.209278+00:00
-- url     : https://prove2.me/theorems/474219f2-7ecb-4429-8cb7-e453b4289191
-- title:
--   Fact 3 — $x_i(b+\Delta)\ge B^{(k)}(b)$, and $x_i(b)\ge B^{(k)}(b)$ without atoms
-- statement:
--   Consider one $k$-unit first-price auction with $n$ agents, value laws $V$ and any strategy profile $E$. Let $x_i$ be agent $i$'s interim allocation (uniform tie-breaking) and $B^{(k)}$ the distribution function of the $k$-th highest bid. For every bid $b\ge 0$ and every agent $i$:
--   $$x_i(b+\Delta)\ \ge\ B^{(k)}(b)\quad\text{for all }\Delta>0,$$
--   and if no agent's marginal bid distribution has an atom, then $x_i(b)\ge B^{(k)}(b)$.
--
--   This relates the order statistic of the bids to an individual agent's chance of winning. It is used to lower-bound utilities in Theorem 1 and Lemma 4.
--
--   Differences from the source:
--   - encoding: a strategy is a map E_i : V_i → Δ(ℝ≥0) from values to bid distributions → a Markov kernel E i : Kernel ℝ ℝ with E i v ((−∞, 0)) = 0 for every v; reason: measurability in v is what makes the marginal bid distribution ∫ E_{i,v} dV_i defined; a law on ℝ with no mass below 0 is a law on ℝ≥0
--   - encoding: B^(k)(b) = Pr[k-th highest bid ≤ b] = Pr[#{j : b_j > b} ≤ k − 1] → Pr[#{j : b_j > b} < k]; reason: identical for k ≥ 1; at k = 0 both sides of Fact 3 involve B = 0
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 45, Fact 3 (Appendix A.2)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions

open MeasureTheory ProbabilityTheory

namespace LargeSupplyFPA.Asymptotic

theorem fact_3 {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (b : ℝ) (hb : 0 ≤ b) (i : Fin n) :
    (∀ Δ : ℝ, 0 < Δ → kthBidCDF k V E b ≤ alloc k V E i (b + Δ)) ∧
      (IsAtomless V E → kthBidCDF k V E b ≤ alloc k V E i b) := by sorry

end LargeSupplyFPA.Asymptotic
