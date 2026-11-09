-- Prove2me | Theorems.Thm_NashAmplification_Filtering_lemma_3_2
-- name    : NashAmplification.Filtering.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:26:49.22978+00:00
-- url     : https://prove2.me/theorems/def94977-0d74-40ca-865a-0836fee7fe8d
-- title:
--   Lemma 3.2 — sampling functions of several sequences
-- statement:
--   Let $k\ge2$, $C\ge2$, $t\ge1$, and let $A$ be the tuple set of a $k$-player game with finite nonempty action sets. Let $\sigma_j$ be probability distributions on $A^t$ and $P=C^{-1}\sum_j\sigma_j$. Fix a set $I\subseteq[C]$ with real upper bound $\ell$ satisfying $|I|\le\ell$, arbitrary sequences for its coordinates, and draw all other coordinates independently according to their original $\sigma_j$. Let $f:(A^t)^{k-1}\to[0,1]$, with argument order significant. The empirical average includes every ordered tuple of player indices, including repetitions. Then
--   $$\mathbb E\left|\frac1{C^{k-1}}\sum_{j_1,\ldots,j_{k-1}}f(Y_{j_1},\ldots,Y_{j_{k-1}})-\mathbb E_{P^{\otimes(k-1)}}f\right|\le\frac{k}{2\sqrt C}+\frac{k\ell+\binom{k}{2}}C.$$
--   The outer law fixes $I$ and samples the remaining players independently; the inner law draws $k-1$ fresh independent sequences from the original mixture $P$. This estimate accounts for repeated empirical indices without identifying the arguments of $f$.
--
--   Differences from the source:
--   - encoding: finite nonempty action sets and one-based player indices → positive action counts with Fin indices, mixed-radix table order, and zero-based coordinates; reason: finite relabeling preserves every source game and distribution
--   - encoding: rounds s=1,...,t and expectations over independent remaining draws → Fin t coordinate r denotes s=r+1, with explicit finite weighted sums; reason: the finite-sum law is precisely the stated product law, including I empty or full
--   - generalization: the surrounding section fixes t,C by (2.10),(2.23) and a failed recovery profile → any t≥1, C≥2 and mixed profile on the resulting sequence space; reason: the sampling estimate does not use failure or game payoffs; no restriction on t,C beyond positivity is used
--   - generalization: a fixed-coordinate count bound |I|≤ℓ → any real upper bound ℓ with (|I|:ℝ)≤ℓ; reason: the estimate is monotone in the upper bound and includes every integer count bound without rounding
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Lemma 3.2, PDF p. 15 (printed p. 14); statement continues PDF p. 16 (printed p. 15)

import Definitions.Def_NashAmplification_Filtering_Process

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Lemma 3.2, PDF 15–16: ordered index tuples include repetitions. -/
theorem lemma_3_2 {k C t : ℕ} (hk : 2 ≤ k) (hC : 2 ≤ C) (ht : 1 ≤ t)
    {n : Fin k → ℕ} (hn : ∀ r, 0 < n r)
    (σ : Fin C → Seq n t → ℝ) (hσ : AGT.IsMixedProfile σ)
    (I : Finset (Fin C)) (ℓ : ℝ) (hI : (I.card : ℝ) ≤ ℓ) (fixed : Fin C → Seq n t)
    (f : (Fin (k-1) → Seq n t) → ℝ) (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1) :
    fixedExpectation σ I fixed (fun y =>
      |(∑ js : Fin (k-1) → Fin C, f (fun d => y (js d))) / (C : ℝ)^(k-1) -
        ∑ z : Fin (k-1) → Seq n t, (∏ d, mixture σ (z d)) * f z|) ≤
      (k : ℝ) / (2 * Real.sqrt C) +
        ((k : ℝ) * ℓ + (Nat.choose k 2 : ℝ)) / C := by sorry
end NashAmplification.Filtering
