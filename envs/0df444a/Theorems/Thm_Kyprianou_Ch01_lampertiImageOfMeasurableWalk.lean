-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiImageOfMeasurableWalk
-- name    : Kyprianou.Ch01.lampertiImageOfMeasurableWalk
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:39:27.90966+00:00
-- url     : https://prove2.me/theorems/714f50a8-cfe7-4a59-85a1-42c6291e19dd
-- title:
--   Lamperti image of a jointly measurable walk is jointly measurable
-- statement:
--   Let $X:\Omega\times[0,\infty)\to\mathbb{Z}$ be jointly measurable.
--
--   The reverse Lamperti image
--   $$(\omega,s)\mapsto Y_s(\omega)$$
--   obtained from $X$ by the occupation clock and the first negative passage is jointly measurable.
-- source:
--   Kyprianou (2006), Section 1.3.4; the frozen population is the Lamperti image of the shifted lattice walk.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiImageOfMeasurableWalk
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    Measurable
      (fun p : Ω × ℝ≥0 => compoundPoissonToBranching X p.2 p.1) := by
  sorry
