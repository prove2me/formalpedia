-- Prove2me | Theorems.Thm_LemonsPoA_TwoSided_lemma_3_4
-- name    : LemonsPoA.TwoSided.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:11:22.890426+00:00
-- url     : https://prove2.me/theorems/73595cba-df8f-445b-9cbd-dfd3b798bbdc
-- title:
--   Lemma 3.4 — screening bound: a log-concave survival function gives $u(k)\ge \frac1e E[(\hat v_B-k)_+]$
-- statement:
--   Let $\hat v_B$ be an integrable real random variable with law $\nu$ whose survival function $t\mapsto\Pr[\hat v_B>t]$ is log-concave on $\mathbb R$, and let $u(k)=\sup_{q>k}(q-k)\Pr[\hat v_B>q]$ be the continuous monopoly profit (32). Then for every $k\in\mathbb R$,
--   $$u(k)\ \ge\ \frac1e\,E\big[(\hat v_B-k)_+\big].$$
--
--   This is the screening step: posting one price captures a $1/e$ fraction of the expected surplus above any reservation value.
--
--   Differences from the source:
--   - encoding: the integrable buyer value $\hat v_B$ → its probability law $\nu$ on $\mathbb R$, with `Integrable id ν`; reason: the survival function, $u(k)$ and $E[(\hat v_B-k)_+]$ depend only on this law
--   - encoding: log-concave function → `ConvexOptimization.LogConcaveOn Set.univ` (power form $f(a)^s f(b)^{1-s}\le f(sa+(1-s)b)$, $f\ge 0$); reason: the same condition, written so that zero values are allowed
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), p. 20, Lemma 3.4

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_LemonsPoA_TwoSided_Monopoly

open MeasureTheory

namespace LemonsPoA.TwoSided

/-- Lemma 3.4 (p. 20): an integrable buyer value with a log-concave survival function has
continuous monopoly profit `u(k) ≥ (1/e) E[(v̂_B - k)_+]` at every reservation value `k`. -/
theorem lemma_3_4 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : Integrable id ν)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ (survival ν)) (k : ℝ) :
    1 / Real.exp 1 * ∫ t, max (t - k) 0 ∂ν ≤ u ν k := by sorry

end LemonsPoA.TwoSided
