-- Prove2me | Theorems.Thm_NashAmplification_Filtering_proposition_2_5
-- name    : NashAmplification.Filtering.proposition_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:26:53.671935+00:00
-- url     : https://prove2.me/theorems/e18cbf7d-1f2a-4387-b150-3ea076d3e9ea
-- title:
--   Proposition 2.5 — upper bound on average payoff
-- statement:
--   For the game $H$ from the payoff calculation, with $k\ge2$, $C\ge2$, $t\ge1$, nonempty finite input action sets, payoffs in $[0,1]$, $q=1-\beta/2$, $h=\Delta/4$ and $\beta,\Delta\in(0,1)$, every real mixed profile $\sigma$ satisfies
--   $$\frac1C\sum_i U_i(\sigma)\le q^t.$$
--   Expected payoffs use independent choices by all players. This is the uniform upper bound on average payoff used in the reduction.
--
--   Differences from the source:
--   - encoding: finite nonempty action sets and one-based player indices → positive action counts with Fin indices, mixed-radix table order, and zero-based coordinates; reason: finite relabeling preserves every source game and distribution
--   - generalization: rational β,Δ satisfying (2.5), with t and C selected by (2.10) and (2.23) → all real β and Δ in (0,1), every t≥1 and C≥2; reason: these structural, mass and error estimates need only the displayed ranges, not β+kΔ<δ or the particular t,C choices; every source choice specializes directly
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Proposition 2.5, PDF p. 10 (printed p. 9)

import Definitions.Def_NashAmplification_Filtering_Process

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Proposition 2.5, PDF 10, (2.16). -/
theorem proposition_2_5 {k C t : ℕ} (hk : 2 ≤ k) (hC : 2 ≤ C) (ht : 1 ≤ t)
    {n : Fin k → ℕ} (hn : ∀ r, 0 < n r) (u : Utility n) (hu : BoundedGame u)
    (β Δ : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hΔ : Δ ∈ Set.Ioo (0 : ℝ) 1)
    (σ : Fin C → Seq n t → ℝ) (hσ : AGT.IsMixedProfile σ) :
    (∑ i : Fin C, AGT.expectedPayoff (payoff u (1-β/2) (Δ/4)) σ i) / C ≤
      (1-β/2)^t := by sorry
end NashAmplification.Filtering
