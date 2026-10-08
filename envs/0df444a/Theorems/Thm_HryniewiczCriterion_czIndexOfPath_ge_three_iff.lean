-- Prove2me | Theorems.Thm_HryniewiczCriterion_czIndexOfPath_ge_three_iff
-- name    : HryniewiczCriterion.czIndexOfPath_ge_three_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T22:16:14.76499+00:00
-- url     : https://prove2.me/theorems/229f3be3-6486-46a3-849c-8be50c75a882
-- title:
--   The index threshold three is equivalent to winding strictly above one
-- statement:
--   Suppose the winding set of a matrix path is $[a,b]$, with $a\le b$ and $b-a<1$. Then the lower semicontinuous index defined from its endpoints satisfies $\mu\ge3$ if and only if every element of the winding set is strictly greater than $1$. This includes integer endpoints and needs no regularity assumption beyond the stated interval description.
-- source:
--   Hryniewicz, https://arxiv.org/html/1105.2077v5#S2.SS1.SSS1, Section 2.1.1, pp. 5–6, the winding interval and equations (4)–(5).

import Definitions.Def_HryniewiczCriterion_ConleyZehnder

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.czIndexOfPath_ge_three_iff (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ)
    (hab : a ≤ b) (hw : windingInterval φ = Set.Icc a b) (hwidth : b - a < 1) :
    3 ≤ czIndexOfPath φ ↔ ∀ d ∈ windingInterval φ, 1 < d := by sorry
