-- Prove2me | Theorems.Thm_NashAmplification_Filtering_lemma_3_1
-- name    : NashAmplification.Filtering.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:26:45.852871+00:00
-- url     : https://prove2.me/theorems/73c63b71-bf3c-4303-964e-1f533a2043db
-- title:
--   Lemma 3.1 — sampling bound with fixed sequences
-- statement:
--   Let $k\ge2$, $C\ge2$, $t\ge1$, and let $\sigma_j$ be probability distributions on the sequence set $A^t$ of a game with finite nonempty action sets. Put $P=C^{-1}\sum_j\sigma_j$. Fix $I\subseteq[C]$ with real upper bound $\ell$ satisfying $|I|\le\ell$, arbitrary sequence values for its coordinates, and $f:A^t\to[0,1]$. Draw all remaining coordinates independently from their original distributions. Then
--   $$\mathbb E\left|C^{-1}\sum_j f(Y_j)-\mathbb E_{z\sim P}f(z)\right|\le\frac\ell C+\frac1{2\sqrt C}.$$
--   The inner draw is fresh and $P$ retains all original component distributions. The estimate permits $I$ to be empty or all players and supplies the fixed-coordinate sampling bound.
--
--   Differences from the source:
--   - encoding: finite nonempty action sets and one-based player indices → positive action counts with Fin indices, mixed-radix table order, and zero-based coordinates; reason: finite relabeling preserves every source game and distribution
--   - encoding: rounds s=1,...,t and expectations over independent remaining draws → Fin t coordinate r denotes s=r+1, with explicit finite weighted sums; reason: the finite-sum law is precisely the stated product law, including I empty or full
--   - generalization: the surrounding section fixes t,C by (2.10),(2.23) and a failed recovery profile → any t≥1, C≥2 and mixed profile on the resulting sequence space; reason: neither the statement nor its proof uses failure or game payoffs; no restriction on t,C beyond positivity is used
--   - generalization: a fixed-coordinate count bound |I|≤ℓ → any real upper bound ℓ with (|I|:ℝ)≤ℓ; reason: the estimate is monotone in the upper bound and includes every integer count bound without rounding
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Lemma 3.1, PDF p. 14 (printed p. 13)

import Definitions.Def_NashAmplification_Filtering_Process

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Lemma 3.1, PDF 14, including the fixed-coordinate bias. -/
theorem lemma_3_1 {k C t : ℕ} (hk : 2 ≤ k) (hC : 2 ≤ C) (ht : 1 ≤ t)
    {n : Fin k → ℕ} (hn : ∀ r, 0 < n r)
    (σ : Fin C → Seq n t → ℝ) (hσ : AGT.IsMixedProfile σ)
    (I : Finset (Fin C)) (ℓ : ℝ) (hI : (I.card : ℝ) ≤ ℓ) (fixed : Fin C → Seq n t)
    (f : Seq n t → ℝ) (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1) :
    fixedExpectation σ I fixed (fun y =>
      |(∑ j, f (y j)) / C - ∑ z, mixture σ z * f z|) ≤
      ℓ / C + 1 / (2 * Real.sqrt C) := by sorry
end NashAmplification.Filtering
