-- Prove2me | Theorems.Thm_NashAmplification_Filtering_lemma_3_3
-- name    : NashAmplification.Filtering.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:31:00.109286+00:00
-- url     : https://prove2.me/theorems/3f9f7271-d7e9-40d5-bce4-34e8d6bc9715
-- title:
--   Lemma 3.3 — one-round weight comparison
-- statement:
--   Let $k\ge2$, $C\ge2$, $t\ge1$, let $G$ have finite nonempty action sets and payoffs in $[0,1]$, and let $\beta,\Delta\in(0,1)$ with $q=1-\beta/2$, $h=\Delta/4$. Fix a mixed profile $\sigma$ on which every recovery test fails and a deviator $i$. For every round $1\le s\le t$ and every profile $Y$ with $Y_i=z^*$ from recovery on the original $\sigma$,
--   $$e_s^W\le2e_{s-1}^W+\frac2h e_s^V+\left|\frac1C\sum_j W_s(Y_j)-q^s\right|.$$
--   The errors compare the hatted calculation on $Y$ with the original recovery calculation. This is a deterministic comparison for each realized profile.
--
--   Differences from the source:
--   - encoding: finite nonempty action sets and one-based player indices → positive action counts with Fin indices, mixed-radix table order, and zero-based coordinates; reason: finite relabeling preserves every source game and distribution
--   - generalization: rational β,Δ satisfying (2.5), with t and C selected by (2.10) and (2.23) → all real β and Δ in (0,1), every t≥1 and C≥2; reason: these structural, mass and error estimates need only the displayed ranges, not β+kΔ<δ or the particular t,C choices; every source choice specializes directly
--   - encoding: rounds s=1,...,t and expectations over independent remaining draws → Fin t coordinate r denotes s=r+1, with explicit finite weighted sums; reason: the finite-sum law is precisely the stated product law, including I empty or full
--   - generalization: every realization of the deviation experiment → every pure profile with Y_i=z* including zero-probability profiles; reason: the deterministic comparison requires no support assumption
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Lemma 3.3, PDF p. 16 (printed p. 15)

import Definitions.Def_NashAmplification_Filtering_Errors

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Lemma 3.3, PDF 16, (3.10), source round s = r.val+1. -/
theorem lemma_3_3 {k C t : ℕ} (hk : 2 ≤ k) (hC : 2 ≤ C) (ht : 1 ≤ t)
    {n : Fin k → ℕ} (hn : ∀ r, 0 < n r) (u : Utility n) (hu : BoundedGame u)
    (β Δ : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hΔ : Δ ∈ Set.Ioo (0 : ℝ) 1)
    (σ : Fin C → Seq n t → ℝ) (hσ : AGT.IsMixedProfile σ)
    (hfail : recoveryRound u β Δ σ = none) (i : Fin C) (r : Fin t) (y : Fin C → Seq n t)
    (hy : y i = zStar hn u β Δ σ) :
    errorW u β Δ σ (r.val+1) y ≤
      2 * errorW u β Δ σ r.val y + (2 / (Δ/4)) * errorV u β Δ σ r y +
      |(∑ j, weights u (1-β/2) (Δ/4) (mixture σ) (r.val+1) (y j)) / C -
        (1-β/2)^(r.val+1)| := by sorry
end NashAmplification.Filtering
