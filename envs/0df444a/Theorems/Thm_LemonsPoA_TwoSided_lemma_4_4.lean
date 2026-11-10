-- Prove2me | Theorems.Thm_LemonsPoA_TwoSided_lemma_4_4
-- name    : LemonsPoA.TwoSided.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:11:32.771245+00:00
-- url     : https://prove2.me/theorems/2b5254fd-138c-4a0e-af80-ceb9a6d92106
-- title:
--   Lemma 4.4 — log-concave $Z$ and an independent copy: $\frac{\sqrt{\mathrm{Var} Z}}2\le E[(Z-Z')_+]\le\frac{\sqrt{\mathrm{Var} Z}}{\sqrt2}$
-- statement:
--   Let $Z$ be an integrable random variable with a log-concave density, and let $Z'$ be an independent copy. Then $Z$ has finite variance, and
--   $$\frac{\sqrt{\mathrm{Var}(Z)}}{2}\ \le\ E\big[(Z-Z')_+\big]\ \le\ \frac{\sqrt{\mathrm{Var}(Z)}}{\sqrt2}.$$
--   The same inequalities hold when $Z$ is constant.
--
--   The lemma compares the first-best gains from trade between two independent draws with the standard deviation.
--
--   **Formalization Note** $Z$ enters through its law $\nu$; $E[(Z-Z')_+]=\int(z-z')_+\,d(\nu\otimes\nu)$; "finite variance" is `MemLp id 2 ν`; the constant case is $\nu$ a point mass (`LogConcaveOrConst`).
--
--   Differences from the source:
--   - encoding: log-concave function → `ConvexOptimization.LogConcaveOn Set.univ` (power form $f(a)^s f(b)^{1-s}\le f(sa+(1-s)b)$, $f\ge 0$); reason: the same condition, written so that zero values are allowed
--   - encoding: $Z$ and an independent copy $Z'$ → the law $\nu$ of $Z$ and the product law $\nu\otimes\nu$; reason: all quantities depend only on the joint law of $(Z,Z')$
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), p. 22, Lemma 4.4

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Distributions

open MeasureTheory ProbabilityTheory

namespace LemonsPoA.TwoSided

/-- Lemma 4.4 (p. 22): an integrable `Z` (law `ν`) with a log-concave density, or a constant
`Z`, has finite variance, and for an independent copy `Z'`,
`√Var(Z)/2 ≤ E[(Z - Z')_+] ≤ √Var(Z)/√2`. -/
theorem lemma_4_4 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : Integrable id ν)
    (hlc : LogConcaveOrConst ν) :
    MemLp id 2 ν ∧
      Real.sqrt (variance id ν) / 2 ≤ ∫ z, max (z.1 - z.2) 0 ∂(ν.prod ν) ∧
      ∫ z, max (z.1 - z.2) 0 ∂(ν.prod ν) ≤ Real.sqrt (variance id ν) / Real.sqrt 2 := by sorry

end LemonsPoA.TwoSided
