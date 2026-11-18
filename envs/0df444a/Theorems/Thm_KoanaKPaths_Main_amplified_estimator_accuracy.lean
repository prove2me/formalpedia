-- Prove2me | Theorems.Thm_KoanaKPaths_Main_amplified_estimator_accuracy
-- name    : KoanaKPaths.Main.amplified_estimator_accuracy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:26:36.4894+00:00
-- url     : https://prove2.me/theorems/82d4fd41-d43e-440d-919d-b9d708c03eb4
-- title:
--   Accuracy of the amplified determinant-sketch estimator
-- statement:
--   Let $c$ be any homogeneous degree-$k$ zero-one coefficient tensor over $n\ge1$ variables, with $k\ge1$, and let $N$ be its number of multilinear monomials. Take positive real tolerances $\varepsilon,\delta$ and their controls
--
--   $$
--   a=\left\lceil\log_2(1/\varepsilon)\right\rceil_+,
--   \qquad b=\left\lceil\log_2(1/\delta)\right\rceil_+.
--   $$
--
--   Use mutually independent uniform signs for every label and sketch matrix in every trial, with sketch width $k$. Each of $2b+1$ groups averages $1024k^3 4^a$ trials, and $\widehat N$ is the median of these group averages. Then
--
--   $$
--   \Pr\!\left[|\widehat N-N|\le\varepsilon N\right]\ge1-\delta.
--   $$
--
--   The probability is the uniform fraction of all finite trial arrays. The estimate is a written rational with a common positive denominator; $N=0$ is included. This establishes the statistical part of the counting theorem. Efficient evaluation and a bit-time machine bound are separate requirements.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed p. 5 / PDF p. 6, Section 3 (median-of-means), printed p. 8 / PDF p. 9, Lemma 6 and its following paragraph; graph coefficient tensor: printed p. 9 / PDF p. 10, Section 4.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Definitions.Def_KoanaKPaths_GraphEstimator
import Definitions.Def_KoanaKPaths_Main_Inputs
import Theorems.Thm_KoanaKPaths_Main_recursive_estimator_moments
set_option synthInstance.maxSize 4096
open KoanaKPaths.Main

theorem KoanaKPaths.Main.amplified_estimator_accuracy (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (c : (Fin k → Fin n) → ℤ) (hc : IsZeroOneTensor c)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    1-δ ≤ uniformMean (fun w :
      Fin (2*ctrl δ+1) → Fin (groupTrials k (ctrl ε)) → Labels n k × SketchSigns n k k =>
      if |(((estimateFraction c (ctrl ε) (ctrl δ) w).val : ℚ) : ℝ)-(tensorN c : ℝ)| ≤
          ε*(tensorN c : ℝ) then (1 : ℝ) else 0) := by sorry
