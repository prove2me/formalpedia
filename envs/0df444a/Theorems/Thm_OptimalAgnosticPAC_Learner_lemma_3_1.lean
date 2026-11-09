-- Prove2me | Theorems.Thm_OptimalAgnosticPAC_Learner_lemma_3_1
-- name    : OptimalAgnosticPAC.Learner.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:48.871882+00:00
-- url     : https://prove2.me/theorems/117e3e3c-d6d1-4782-bba4-2f7d5e8c027c
-- title:
--   Lemma 3.1: reverse martingale
-- statement:
--   Let $Z_i=(X_i,Y_i)$, $1\le i\le2k$, $k\ge1$, be i.i.d. observations from $P$, let $q$ be a symmetric score satisfying (13), and let $q_t(x)=q(x;(Z_1,\dots,Z_t))$. Fix $h\in\mathcal H$ and, for $k\le t\le2k-1$, let
--   $$\Delta_{t+1,h}=\ell(q_t(X_{t+1}),Y_{t+1})-\mathbf 1\{h(X_{t+1})\ne Y_{t+1}\}.$$
--   For every $0<\delta\le1/3$, with probability at least $1-2\delta$,
--   $$\frac1k\max\Bigl(\sum_{m=k+1}^{2k}\Delta_{m,h},0\Bigr)\le8200\Bigl(\sqrt{\frac{L(h)(d+\log(1/\delta))}{k}}+\frac{d+\log(1/\delta)}{k}\Bigr).\tag{16}$$
--
--   This controls the realized excess loss of the sequential scores on the held-out observations.
--
--   Differences from the source:
--   - encoding: labels in {−1,+1}, inputs in a set X → labels in Bool with true for +1, signed values through sgn, X : Type; reason: the reused vcDim takes Bool-valued functions on a Type; renaming the two labels changes no quantity
--   - generalization: q is the symmetrized score of §3.1 satisfying (13) → q is any family with IsLOOScore H d q (values in [−1,1], symmetric, jointly measurable, (13)); reason: the paper's proofs use only these properties, and the paper's q is one such family
--   - generalization: VC(H) = d ≥ 1 → vcDim H ≤ d with d ≥ 1; reason: the bound is increasing in d, so taking d = VC(H) gives the source's statement
--   - encoding: 1-based observations Z_1, …, Z_2k and sum over m = k+1, …, 2k → 0-based Fin (2k) with sum over k ≤ t, where t = m − 1; reason: the same observations in the same order
--   - encoding: with probability at least 1 − 2δ → the sample law (outer measure) of the failure set is bounded by one minus that level; reason: the two agree on measurable events and the failure bound never overstates the probability
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §3.2, Lemma 3.1, PDF pp. 9–10 (printed pp. 8–9)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_OptimalAgnosticPAC_Learner_Score
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- Lemma 3.1, PDF pp. 9–10: inequality (16) fails with probability at most `2δ`. -/
theorem lemma_3_1 {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞))
    (hmeas : ∀ h ∈ H, Measurable h)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (hq : IsLOOScore H d q)
    (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (k : ℕ) (hk : 1 ≤ k) (h : X → Bool) (hh : h ∈ H)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    sampleLaw P (2 * k)
      {S | 8200 * (Real.sqrt (risk P h * ((d : ℝ) + Real.log (1 / δ)) / (k : ℝ)) +
            ((d : ℝ) + Real.log (1 / δ)) / (k : ℝ)) <
          (1 / (k : ℝ)) * max (excessLossSum q h k S) 0} ≤
      ENNReal.ofReal (2 * δ) := by sorry

end OptimalAgnosticPAC.Learner
