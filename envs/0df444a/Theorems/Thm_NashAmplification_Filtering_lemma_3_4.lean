-- Prove2me | Theorems.Thm_NashAmplification_Filtering_lemma_3_4
-- name    : NashAmplification.Filtering.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:30:24.842206+00:00
-- url     : https://prove2.me/theorems/47bf5461-aec2-49a7-9a2a-2f87c455febd
-- title:
--   Lemma 3.4 — bounds on expected errors
-- statement:
--   Let $G$ be a $k$-player game with $k\ge2$, finite nonempty action sets and payoffs in $[0,1]$. Fix $C\ge2$, $t\ge1$, $\beta,\Delta\in(0,1)$, $q=1-\beta/2$, $h=\Delta/4$, a mixed profile $\sigma$ on $A^t$ for which every recovery test fails, and a deviator $i$. The errors $e_s^W$ and $e_s^V$ are the average absolute weight and score discrepancies between the empirical calculation and recovery on the original profile, and $e_s^*$ is the score discrepancy at its fixed maximizing tuple. Let $E_s^V,E_s^W$ be the explicit coefficients (3.13), with $E_0^W=0$ and $\Gamma_k=3k^2$. In every round $1\le s\le t$,
--   $$\max\{\mathbb E_Y e_s^V,\mathbb E_Y e_s^*\}\le E_s^V/\sqrt C,\qquad\mathbb E_Y e_s^W\le E_s^W/\sqrt C.$$
--   The expectation fixes $Y_i=z^*$ and draws opponents independently from $\sigma_{-i}$. The coefficients depend only on $k,\beta,\Delta,s$, so the bound is uniform in the game, action sets, original profile and deviator; for fixed $k,\beta,\Delta,t$ it implies all three stated $O(C^{-1/2})$ bounds.
--
--   Differences from the source:
--   - encoding: finite nonempty action sets and one-based player indices → positive action counts with Fin indices, mixed-radix table order, and zero-based coordinates; reason: finite relabeling preserves every source game and distribution
--   - generalization: rational β,Δ satisfying (2.5), with t and C selected by (2.10) and (2.23) → all real β and Δ in (0,1), every t≥1 and C≥2; reason: these structural, mass and error estimates need only the displayed ranges, not β+kΔ<δ or the particular t,C choices; every source choice specializes directly
--   - encoding: rounds s=1,...,t and expectations over independent remaining draws → Fin t coordinate r denotes s=r+1, with explicit finite weighted sums; reason: the finite-sum law is precisely the stated product law, including I empty or full
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Lemma 3.4, PDF p. 18 (printed p. 17)

import Definitions.Def_NashAmplification_Filtering_Errors

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Lemma 3.4, PDF 18, both inequalities of (3.14), coefficients (3.13). -/
theorem lemma_3_4 {k C t : ℕ} (hk : 2 ≤ k) (hC : 2 ≤ C) (ht : 1 ≤ t)
    {n : Fin k → ℕ} (hn : ∀ r, 0 < n r) (u : Utility n) (hu : BoundedGame u)
    (β Δ : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hΔ : Δ ∈ Set.Ioo (0 : ℝ) 1)
    (σ : Fin C → Seq n t → ℝ) (hσ : AGT.IsMixedProfile σ)
    (hfail : recoveryRound u β Δ σ = none) (i : Fin C) (r : Fin t) :
    max (deviationExpectation hn u β Δ σ i (errorV u β Δ σ r))
        (deviationExpectation hn u β Δ σ i (errorStar hn u β Δ σ r)) ≤
        (coefficients k β Δ (r.val+1)).1 / Real.sqrt C ∧
    deviationExpectation hn u β Δ σ i (errorW u β Δ σ (r.val+1)) ≤
        (coefficients k β Δ (r.val+1)).2 / Real.sqrt C := by sorry
end NashAmplification.Filtering
