-- Prove2me | Theorems.Thm_LearningBasedRO_iStar_valid_iff
-- name    : LearningBasedRO.iStar_valid_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:56.734986+00:00
-- url     : https://prove2.me/theorems/1912ce69-f7bc-4ed9-ab6a-60312668c1fa
-- title:
--   Validity of (4) — $i^*$ exists $\iff 1-(1-\epsilon)^{n_2}\ge1-\delta \iff n_2\ge\log\delta/\log(1-\epsilon)$
-- statement:
--   Let $0<\epsilon<1$, $0<\delta<1$ and $n_2\in\mathbb N$. The following are equivalent:
--
--   1. the index $i^*$ of (4) can be found, i.e. some $1\le r\le n_2$ satisfies $\sum_{k=0}^{r-1}\binom{n_2}{k}(1-\epsilon)^k\epsilon^{n_2-k}\ge 1-\delta$;
--   2. $1-(1-\epsilon)^{n_2}\ge 1-\delta$;
--   3. $$n_2\ge \frac{\log\delta}{\log(1-\epsilon)} .$$
--
--   This is the sample-size condition of Theorem 1: the procedure is valid exactly when the Phase 2 sample has at least $\log\delta/\log(1-\epsilon)$ points, a number independent of the dimensions of the decision and of the data.
--
--   Differences from the source:
--   - reading: ϵ, δ tolerance and confidence levels (range not stated) → 0 < ϵ < 1, 0 < δ < 1; reason: the meaningful range; log(1 − ϵ) requires ϵ < 1
--   - encoding: "such an i∗ can be found" → the set of (4) (iStarSet) is nonempty; log → Real.log, n₂ cast to ℝ; reason: Lean conventions, same instances
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, (4) and the sentence after it, p.7; proof of Theorem 1, p.9

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

namespace LearningBasedRO

/-- **Validity of (4).** The index `i*` of (4) can be found (its defining set is nonempty) if and
only if `1 - (1 - ϵ)^{n₂} ≥ 1 - δ`, if and only if `n₂ ≥ log δ / log(1 - ϵ)`.
Hong–Huang–Lam, arXiv:1704.04342v2, (4) and the sentence after it, p.7; proof of Theorem 1, p.9.

**Formalization Note** `0 < ϵ < 1` and `0 < δ < 1` (the page's tolerance and confidence levels).
`log` is `Real.log`; `n₂` is cast to `ℝ`. -/
theorem iStar_valid_iff (n₂ : ℕ) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    ((iStarSet n₂ ϵ δ).Nonempty ↔ 1 - δ ≤ 1 - (1 - ϵ) ^ n₂) ∧
      (1 - δ ≤ 1 - (1 - ϵ) ^ n₂ ↔ Real.log δ / Real.log (1 - ϵ) ≤ (n₂ : ℝ)) := by sorry

end LearningBasedRO
