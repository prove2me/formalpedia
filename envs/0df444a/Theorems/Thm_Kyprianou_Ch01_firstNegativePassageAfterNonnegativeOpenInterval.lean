-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNegativePassageAfterNonnegativeOpenInterval
-- name    : Kyprianou.Ch01.firstNegativePassageAfterNonnegativeOpenInterval
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T15:22:45.658569+00:00
-- url     : https://prove2.me/theorems/4df6ac29-dc4f-48ad-929e-961947dd6bcf
-- title:
--   First negative passage does not precede a nonnegative open source interval
-- statement:
--   If an integer-valued path is nonnegative at every source time strictly before c, its first strictly negative passage cannot precede c. The firstNegativePassage definition is an extended infimum over t>0 with X(t)<0. Both finite and infinite first passage cases follow from the order definition.
-- source:
--   Kyprianou (2006) §1.3.4, first negative passage of a nonnegative prefix

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNegativePassageAfterNonnegativeOpenInterval
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω) (c : ℝ≥0)
    (hNonneg : ∀ u : ℝ≥0, u < c → 0 ≤ X u ω) :
    (c : WithTop ℝ≥0) ≤ firstNegativePassage X ω := by
  sorry
