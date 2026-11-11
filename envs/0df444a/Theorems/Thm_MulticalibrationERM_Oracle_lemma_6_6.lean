-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_lemma_6_6
-- name    : MulticalibrationERM.Oracle.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:52:40.629849+00:00
-- url     : https://prove2.me/theorems/e769854e-aa96-4282-9fe7-2fe43c3ca6ad
-- title:
--   Lemma 6.6 — variance budget of the confidence-interval and partition construction
-- statement:
--   There is an absolute constant $C$ such that, when $X$ carries a total order with measurable order intervals (Remark 2.7), for the construction of §6.3 (a confidence sample of $n_{\mathrm{conf}}\ge1$ labeled examples and an independent partition sample of $n_{\mathrm{part}}\ge1$ inputs, both i.i.d. from $D$, $\delta_0\in(0,1)$), with probability at least $1-2\delta_0$,
--   $$V_P\le C\Big(\frac{\log(en_{\mathrm{conf}}/\delta_0)}{n_{\mathrm{conf}}}+\frac{\log(en_{\mathrm{part}}/\delta_0)}{n_{\mathrm{part}}}\Big).$$
--
--   Differences from the source:
--   - encoding: sample sizes n_conf, n_part → n_conf ≥ 1 and n_part ≥ 1; reason: nondegeneracy: the right side divides by them
--   - encoding: a computable total order with measurable order intervals (Remark 2.7) → a LinearOrder on X whose open/closed intervals and open rays are measurable; computability is not modelled; reason: computability does not affect the statement
--   - encoding: independent confidence and partition samples → consecutive blocks of one i.i.d. stream from D (positions 0..n_conf−1, then the inputs of the next n_part); reason: disjoint blocks of an i.i.d. stream are independent i.i.d. samples
--   - encoding: empty cells are discarded → empty cells are kept and contribute D_X(∅)² = 0; reason: no change to V_P
--   - encoding: probability of the failure event → the measure applied to the failure set, i.e. its outer measure when the set is not measurable; reason: equal to the probability when the event is measurable; an outer-measure bound is never weaker
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 34, Lemma 6.6

import Mathlib
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_OEMC

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Lemma 6.6 (p. 34): variance budget of the construction of Section 6.3. `X` carries a total
order whose order intervals are measurable (Remark 2.7). The confidence sample is
`s 0, …, s (n_conf − 1)` and the partition sample is the inputs of `s n_conf, …,
s (n_conf + n_part − 1)`, all i.i.d. from `D`. With probability at least `1 − 2δ₀`,
`V_P ≤ C (log(e n_conf/δ₀)/n_conf + log(e n_part/δ₀)/n_part)` for an absolute constant `C`. -/
theorem lemma_6_6 :
    ∃ C : ℝ, 0 < C ∧
    ∀ {X : Type} [MeasurableSpace X] [LinearOrder X], OrderIntervalsMeasurable X →
    ∀ (D : LabeledDist X) (nconf npart : ℕ), 1 ≤ nconf → 1 ≤ npart →
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < 1 →
      (Measure.infinitePi fun _ : ℕ => D.μ)
          {s | C * (Real.log (Real.exp 1 * nconf / δ₀) / nconf +
                Real.log (Real.exp 1 * npart / δ₀) / npart) <
              constructionBudget D s nconf npart nconf δ₀} ≤
        ENNReal.ofReal (2 * δ₀) := by sorry

end MulticalibrationERM.Oracle
