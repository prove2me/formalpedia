-- Prove2me | Theorems.Thm_LemonsPoA_TwoSided_theorem_4_5
-- name    : LemonsPoA.TwoSided.theorem_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:11:35.393685+00:00
-- url     : https://prove2.me/theorems/299d4cb5-af93-4dc8-85f9-8890e652c202
-- title:
--   Theorem 4.5 (Barlow–Marshall–Proschan) — an MHR variable with finite mean has $E[T^2]\le 2(E[T])^2$
-- statement:
--   Let $T$ be a nonnegative random variable with a density, a nondecreasing hazard rate, and finite mean. Then $T$ has finite second moment, and
--   $$E[T^2]\ \le\ 2\,(E[T])^2.$$
--
--   This classical moment comparison (Barlow, Marshall and Proschan 1963, Theorem 4.3) is used to show that log-concave variables have finite variance comparable to their mean absolute deviation.
--
--   **Formalization Note** $T$ enters through its law $\nu$ on $\mathbb R$ with $\nu((-\infty,0))=0$. The hazard rate is $h(t)=f(t)/\Pr[T>t]$ for a version $f$ of the density; it is required nondecreasing on $\{t\ge 0:\Pr[T>t]>0\}$ (`HasMHRDensity`).
--
--   Differences from the source:
--   - encoding: a nonnegative random variable with a density and a nondecreasing hazard rate → its law $\nu$ on $\mathbb R$ with $\nu((-\infty,0))=0$ and some Lebesgue density $f\ge 0$ with $t\mapsto f(t)/\nu((t,\infty))$ nondecreasing on $\{t\ge 0:\nu((t,\infty))>0\}$; reason: the hazard rate is defined where the survival function is positive, and a density is defined up to null sets, so the condition is on some version
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), p. 23, Theorem 4.5

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Distributions

open MeasureTheory

namespace LemonsPoA.TwoSided

/-- Theorem 4.5 (Barlow–Marshall–Proschan, p. 23): a nonnegative random variable `T` (law `ν`)
with a density, a nondecreasing hazard rate and finite mean has a finite second moment and
`E[T²] ≤ 2 (E[T])²`. -/
theorem theorem_4_5 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hnn : ν (Set.Iio 0) = 0)
    (hmhr : HasMHRDensity ν) (hν : Integrable id ν) :
    Integrable (fun t => t ^ 2) ν ∧ ∫ t, t ^ 2 ∂ν ≤ 2 * (∫ t, t ∂ν) ^ 2 := by sorry

end LemonsPoA.TwoSided
