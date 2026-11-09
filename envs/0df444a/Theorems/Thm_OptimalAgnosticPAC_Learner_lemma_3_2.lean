-- Prove2me | Theorems.Thm_OptimalAgnosticPAC_Learner_lemma_3_2
-- name    : OptimalAgnosticPAC.Learner.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:56.819521+00:00
-- url     : https://prove2.me/theorems/df7e47fd-6b48-4f99-a62c-1fa61b8724d2
-- title:
--   Lemma 3.2: forward martingale
-- statement:
--   Under the assumptions and notation of Lemma 3.1, for every $0<\delta\le1/3$, with probability at least $1-\delta$,
--   $$\frac1k\sum_{t=k}^{2k-1}\bigl(L(q_t)-L(h)\bigr)\le\frac2k\max\Bigl(\sum_{m=k+1}^{2k}\Delta_{m,h},0\Bigr)+5\sqrt{\frac{L(h)\log(1/\delta)}{k}}+10\frac{\log(1/\delta)}{k}.\tag{17}$$
--   Here $L(q_t)$ is the risk of the score $q_t$ on an independent test point, given the sample.
--
--   This compares the population excess risk of the sequential scores with their realized excess loss.
--
--   Differences from the source:
--   - encoding: labels in {−1,+1}, inputs in a set X → labels in Bool with true for +1, signed values through sgn, X : Type; reason: the reused vcDim takes Bool-valued functions on a Type; renaming the two labels changes no quantity
--   - generalization: q is the symmetrized score of §3.1 satisfying (13) → q is any family with IsLOOScore H d q (values in [−1,1], symmetric, jointly measurable, (13)); reason: the paper's proofs use only these properties, and the paper's q is one such family
--   - generalization: VC(H) = d ≥ 1 → vcDim H ≤ d with d ≥ 1; reason: the bound is increasing in d, so taking d = VC(H) gives the source's statement
--   - encoding: 1-based observations Z_1, …, Z_2k and sum over m = k+1, …, 2k → 0-based Fin (2k) with sum over k ≤ t, where t = m − 1; reason: the same observations in the same order
--   - encoding: with probability at least 1 − δ → the sample law (outer measure) of the failure set is bounded by one minus that level; reason: the two agree on measurable events and the failure bound never overstates the probability
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §3.2, Lemma 3.2, PDF p. 10 (printed p. 9)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_OptimalAgnosticPAC_Learner_Score
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- Lemma 3.2, PDF p. 10: inequality (17) fails with probability at most `δ`. The sum over
`t : Fin (2k)` with `k ≤ t` is the paper's sum over `t = k, …, 2k - 1`. -/
theorem lemma_3_2 {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞))
    (hmeas : ∀ h ∈ H, Measurable h)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (hq : IsLOOScore H d q)
    (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (k : ℕ) (hk : 1 ≤ k) (h : X → Bool) (hh : h ∈ H)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    sampleLaw P (2 * k)
      {S | (2 / (k : ℝ)) * max (excessLossSum q h k S) 0 +
            5 * Real.sqrt (risk P h * Real.log (1 / δ) / (k : ℝ)) +
            10 * (Real.log (1 / δ) / (k : ℝ)) <
          (1 / (k : ℝ)) *
            ∑ t ∈ Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val),
              (scoreRisk P (q t (prefixSample S t t.isLt.le)) - risk P h)} ≤
      ENNReal.ofReal δ := by sorry

end OptimalAgnosticPAC.Learner
