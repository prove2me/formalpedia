-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNegativePassage_eq_rationalInf
-- name    : Kyprianou.Ch01.firstNegativePassage_eq_rationalInf
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T16:49:21.335656+00:00
-- url     : https://prove2.me/theorems/dbc70132-0b09-44e6-9fb1-bffb4d5fc98a
-- title:
--   First negative passage equals rational infimum
-- statement:
--   Let $X$ be an integer-valued path that is jointly measurable in calendar time and the sample point. For each outcome $\omega$, the first strict negative passage equals the extended infimum, over positive rationals $q$, of $q$ on $\{X_q(\omega)<0\}$ and $+\infty$ otherwise.
-- source:
--   Kyprianou (2006), Section 1.3.4; countable determination of first passage.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNegativePassage_eq_rationalInf
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1))
    (ω : Ω) :
    firstNegativePassage X ω =
      ⨅ q : {q : ℚ // 0 < q},
        if X (Real.toNNReal (q : ℝ)) ω < 0 then
          ((Real.toNNReal (q : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤ := by
  sorry
