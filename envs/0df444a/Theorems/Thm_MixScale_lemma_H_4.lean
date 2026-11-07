-- Prove2me | Theorems.Thm_MixScale_lemma_H_4
-- name    : MixScale.lemma_H_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:11:35.005564+00:00
-- url     : https://prove2.me/theorems/59418665-65db-4973-b351-1c3e2e7e22da
-- title:
--   Lemma H.4, p.51 — testing from disjoint parameter balls
-- statement:
--   Suppose two parameter tuples have $D_{\mathrm{par}}>2\varepsilon$ and sample laws with $\chi^2(P_+\|P_-)\le V$. Any possibly randomized estimator from $N$ samples, with parameter error at most $\varepsilon$ with probability at least $2/3$ under both tuples, has
--
--   $$N\ge\frac{2}{9V}.$$
--
--   This converts a chi-square bound on an alternative pair into a sample lower bound.
--
--   Differences from the source:
--   - encoding: supply the estimator with identical deterministic side information → no separate side-information argument; reason: identical deterministic side information is a constant, so an estimator depending on it is one estimator
--   - encoding: N ≥ 2/(9V) → 2 ≤ 9NV in [0, ∞]; reason: the same inequality for 0 < V < ∞; it also covers V = 0 and V = ∞ without division
--   - generalization: sample laws P_± of the two parameter tuples → any probability measures μ_p, μ_m with χ²(μ_p‖μ_m) ≤ V; reason: the proof does not use how the laws arise; the paper's laws are a special case
--   - encoding: every estimator (possibly randomized) → any function of the samples and an independent seed on any probability space, with success via ∃ measurable E ⊆ {success}; reason: a measurable estimator has its ordinary success probability; no measurability is assumed
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Lemma H.4, p.51 (PDF p.53)

import Mathlib
import Definitions.Def_MixScale_Estimator

open MeasureTheory

namespace MixScale

/-- **Lemma H.4** (Testing from disjoint parameter balls).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Lemma H.4, p.51 (PDF p.53).

**Formalization Note.** `V` is in `[0, ∞]`, and `N ≥ 2/(9V)` is `2 ≤ 9 N V` in `ℝ≥0∞`, which also
covers `V = 0` (no estimator exists) and `V = ∞`. The sample laws `μp, μm` may be any probability
measures. Identical deterministic side information is a constant, so an estimator that depends on
it is one estimator here; the seed is common and independent of the samples. -/
theorem lemma_H_4 {d k N : ℕ} (Θp Θm : Params d k) (ε : ℝ) (hsep : 2 * ε < Dpar Θp Θm)
    (μp μm : Measure (Vec d)) [IsProbabilityMeasure μp] [IsProbabilityMeasure μm]
    (V : ENNReal) (hV : chiSq μp μm ≤ V)
    {Sd : Type} [MeasurableSpace Sd] (μS : Measure Sd) [IsProbabilityMeasure μS]
    (est : (Fin N → Vec d) × Sd → Params d k)
    (hp : EstSucceeds μS est (iidLaw N μp) Θp ε (2 / 3))
    (hm : EstSucceeds μS est (iidLaw N μm) Θm ε (2 / 3)) :
    2 ≤ 9 * (N : ENNReal) * V := by sorry

end MixScale
