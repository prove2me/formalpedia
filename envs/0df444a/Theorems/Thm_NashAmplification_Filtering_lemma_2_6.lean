-- Prove2me | Theorems.Thm_NashAmplification_Filtering_lemma_2_6
-- name    : NashAmplification.Filtering.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:30:45.759919+00:00
-- url     : https://prove2.me/theorems/f1689417-8118-4072-82fd-6bfd322a1a60
-- title:
--   Lemma 2.6 — lower bound on deviation payoff
-- statement:
--   Let $G$ have $k\ge2$ players, finite nonempty action sets and payoffs in $[0,1]$. Fix $C\ge2$, $t\ge1$, $\beta,\Delta\in(0,1)$, $q=1-\beta/2$ and $h=\Delta/4$. If every recovery test fails on a mixed profile $\sigma$, form the fixed sequence $z^*$ of first score maximizers from recovery on that original profile. For every player $i$,
--   $$U_i(z^*,\sigma_{-i})=\mathbb E_{Y_{-i}\sim\sigma_{-i}}U_i(z^*,Y_{-i})\ge1-\frac{K}{\sqrt C}.$$
--   Here $K$ is exactly the explicit expression (3.27) in the shared definitions, computed from the recurrence (3.13). It is independent of $G$, $A$, $C$, $\sigma$ and $i$. This is the lower deviation-payoff estimate required by Theorem 1.1.
--
--   Differences from the source:
--   - encoding: finite nonempty action sets and one-based player indices → positive action counts with Fin indices, mixed-radix table order, and zero-based coordinates; reason: finite relabeling preserves every source game and distribution
--   - generalization: rational β,Δ satisfying (2.5), with t and C selected by (2.10) and (2.23) → all real β and Δ in (0,1), every t≥1 and C≥2; reason: these structural, mass and error estimates need only the displayed ranges, not β+kΔ<δ or the particular t,C choices; every source choice specializes directly
--   - encoding: rounds s=1,...,t and expectations over independent remaining draws → Fin t coordinate r denotes s=r+1, with explicit finite weighted sums; reason: the finite-sum law is precisely the stated product law, including I empty or full
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Lemma 2.6, PDF p. 12 (printed p. 11); K is (3.27), PDF p. 22 (printed p. 21)

import Definitions.Def_NashAmplification_Filtering_Errors

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Lemma 2.6, PDF 12, with explicitly defined K from (3.27), PDF 22. -/
theorem lemma_2_6 {k C t : ℕ} (hk : 2 ≤ k) (hC : 2 ≤ C) (ht : 1 ≤ t)
    {n : Fin k → ℕ} (hn : ∀ r, 0 < n r) (u : Utility n) (hu : BoundedGame u)
    (β Δ : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hΔ : Δ ∈ Set.Ioo (0 : ℝ) 1)
    (σ : Fin C → Seq n t → ℝ) (hσ : AGT.IsMixedProfile σ)
    (hfail : recoveryRound u β Δ σ = none) (i : Fin C) :
    DGPNash.NashMap.purePayoff (payoff u (1-β/2) (Δ/4)) σ i (zStar hn u β Δ σ) =
      deviationExpectation hn u β Δ σ i (fun y => payoff u (1-β/2) (Δ/4) i y) ∧
    1 - deviationK k t β Δ / Real.sqrt C ≤
      DGPNash.NashMap.purePayoff (payoff u (1-β/2) (Δ/4)) σ i (zStar hn u β Δ σ) := by sorry
end NashAmplification.Filtering
