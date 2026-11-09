-- Prove2me | Theorems.Thm_OptimalAgnosticPAC_Learner_lemma_3_3
-- name    : OptimalAgnosticPAC.Learner.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:47.964978+00:00
-- url     : https://prove2.me/theorems/bba809fe-079f-4b76-b8a2-7e002488f9e6
-- title:
--   Lemma 3.3: thresholding on a validation sample
-- statement:
--   Let $p:\mathcal X\to[-1,1]$ be measurable and fixed independently of an i.i.d. validation sample $Z_i=(X_i,Y_i)$, $1\le i\le k$, where $k\ge1$. Consider the binary threshold class
--   $$\mathcal T_p=\{x\mapsto2\cdot\mathbf 1\{p(x)\ge u\}-1:-1\le u\le1\}\cup\{x\mapsto-1\}.$$
--   If $\widehat h$ is an empirical risk minimizer over $\mathcal T_p$, then, for every $0<\delta<1$, with probability at least $1-\delta$,
--   $$L(\widehat h)\le\inf_{h\in\mathcal T_p}L(h)+223000\Bigl(\sqrt{\frac{\inf_{h\in\mathcal T_p}L(h)\log(12/\delta)}{k}}+\frac{\log(12/\delta)}{k}\Bigr).$$
--
--   This is the derandomization step: it keeps coefficient one on the best threshold risk.
--
--   Differences from the source:
--   - encoding: labels in {−1,+1}, inputs in a set X → labels in Bool with true for +1, signed values through sgn, X : Type; reason: the reused vcDim takes Bool-valued functions on a Type; renaming the two labels changes no quantity
--   - encoding: p fixed independently of the validation sample → p is a fixed measurable function and the sample has law sampleLaw P k; reason: a deterministic p is independent of the sample; the proof of Theorem 1 conditions on the training block
--   - reading: ĥ is an empirical risk minimizer over T_p, with probability at least 1 − δ → every selection S ↦ ĥ(S) minimizing errors over T_p for each S, with no measurability assumed, and the sample law of the failure set is at most δ; reason: the paper assumes no measurable selection, and a failure bound is meaningful for any selection
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §3.3, Lemma 3.3, PDF p. 14 (printed p. 13)

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Score
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- Lemma 3.3, PDF p. 14: for every empirical risk minimizer selection over `T_p`, on an i.i.d.
validation sample of size `k`, the displayed bound fails with (outer) probability at most `δ`. No
measurability of the selection is assumed. -/
theorem lemma_3_3 {X : Type} [MeasurableSpace X] (P : Measure (X × Bool))
    [IsProbabilityMeasure P] (p : X → ℝ) (hp : Measurable p)
    (hp1 : ∀ x, p x ∈ Set.Icc (-1 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k)
    (hhat : (Fin k → X × Bool) → X → Bool) (hERM : IsERM (thresholdClass p) hhat)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    sampleLaw P k
      {S | minRisk P (thresholdClass p) +
            223000 * (Real.sqrt (minRisk P (thresholdClass p) * Real.log (12 / δ) / (k : ℝ)) +
              Real.log (12 / δ) / (k : ℝ)) <
          risk P (hhat S)} ≤
      ENNReal.ofReal δ := by sorry

end OptimalAgnosticPAC.Learner
