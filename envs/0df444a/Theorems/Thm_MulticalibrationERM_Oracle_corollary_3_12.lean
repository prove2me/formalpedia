-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_corollary_3_12
-- name    : MulticalibrationERM.Oracle.corollary_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:51:13.580222+00:00
-- url     : https://prove2.me/theorems/eb7b11de-8bdd-4b48-a350-e58e71154cf8
-- title:
--   Corollary 3.12 — black-box lower bound in terms of the VC dimension
-- statement:
--   For every $k\ge1$ there is $c_k>0$ such that, for every $\varepsilon\in(0,c_k)$ and every $d$ with $\varepsilon^{-1}\log(1/\varepsilon)/c_k\le d\le\varepsilon^{-k}$, the following holds. If a $\lfloor(d/\varepsilon)^k\rfloor$-query black-box ERM learner, for every class of VC dimension at most $d$, every weighted ERM oracle for it and every distribution, outputs a randomized predictor with multicalibration error at most $\varepsilon$ with probability at least $2/3$, then it uses more than
--   $$\frac{c_k\,d}{\varepsilon^3\log^5(1/\varepsilon)}$$
--   samples.
--
--   As printed, the case $k=1$ is vacuous (for $\varepsilon<c_k<1$ the window $\varepsilon^{-1}\log(1/\varepsilon)/c_k\le d\le\varepsilon^{-1}$ is empty); for every $k>1$ the window is nonempty for all small $\varepsilon$.
--
--   Differences from the source:
--   - reading: a learner that succeeds for every class of VC dimension at most d (on an input set the statement does not fix) → one algorithm for all input sets: a family A X of q-query learners, one per measurable space X, with common sample size n, query budget and seed law; success is required for every X, class, oracle and distribution; reason: the corollary's input set is not fixed (its proof chooses [J] × [D]); the learner must be defined wherever the class lives
--   - generalization: success for every class of VC dimension at most d → success required only for classes with IsAuditorClass H d (measurable members, pointwise measurable); reason: a weaker hypothesis gives a stronger statement; the hard classes of Theorem 3.11 are finite and measurable
--   - encoding: success with probability at least 2/3 → the outer measure of the failure event is at most 1/3; reason: equal to the probability whenever the learner is measurable; the paper's probability is undefined otherwise
--   - encoding: k ≥ 1 (the degree of the polynomials) → real k ≥ 1, with real powers ε^{−k} and (d/ε)^k; reason: the paper does not restrict k to integers
--   - encoding: auditors h : X → {−1,+1} → h : X → Bool with value pm (h x) ∈ {1, −1} (true ↦ +1); reason: relabelling of the two values; every auditor is an instance
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 23, Corollary 3.12

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_ERM
import Definitions.Def_MulticalibrationERM_Oracle_BlackBox

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Corollary 3.12 (p. 23): black-box lower bound in terms of the VC dimension. For every
`k ≥ 1` there is `c_k > 0` such that, for every `ε ∈ (0, c_k)` and every `d` with
`ε⁻¹ log(1/ε)/c_k ≤ d ≤ ε^{−k}`: if a `⌊(d/ε)^k⌋`-query black-box ERM learner, for every class
of VC dimension at most `d` and every distribution (and every weighted ERM oracle for the class),
outputs a randomized predictor with multicalibration error at most `ε` with probability at least
`2/3`, then it uses more than `c_k d/(ε³ log⁵(1/ε))` samples. The learner is one algorithm for all
input sets: a family `A X` of black-box learners, one per input set `X`, sharing the sample size
`n`, the query budget and the seed law; it cannot see the class. -/
theorem corollary_3_12 :
    ∀ k : ℝ, 1 ≤ k → ∃ ck : ℝ, 0 < ck ∧
    ∀ ε : ℝ, 0 < ε → ε < ck → ∀ d : ℕ,
      ε⁻¹ * Real.log (1 / ε) / ck ≤ d → (d : ℝ) ≤ ε ^ (-k) →
    ∀ (n : ℕ) {Ωl : Type} [MeasurableSpace Ωl] (μl : Measure Ωl) [IsProbabilityMeasure μl]
      (A : ∀ (X : Type) [MeasurableSpace X], BBLearner X n ⌊((d : ℝ) / ε) ^ k⌋₊ Ωl),
      (∀ (X : Type) [MeasurableSpace X] (H : Set (X → Bool)), IsAuditorClass H d →
        ∀ {Ωo : Type} [MeasurableSpace Ωo] (νo : Measure Ωo) [IsProbabilityMeasure νo]
          (O : ERMOracle X H 0 Ωo) (D : LabeledDist X),
          bbFailProb (A X) μl O νo D ε ≤ 1 / 3) →
      ck * d / (ε ^ 3 * Real.log (1 / ε) ^ 5) < n := by sorry

end MulticalibrationERM.Oracle
