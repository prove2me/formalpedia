-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroTimeNormalisationAeEq
-- name    : Kyprianou.Ch06.zeroTimeNormalisationAeEq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:06:17.155645+00:00
-- url     : https://prove2.me/theorems/06f924f3-05ce-4c30-bd88-dd0ca835c9bb
-- title:
--   Chapter 6 bridge: time-zero normalisation preserves paths almost surely
-- statement:
--   If a process starts at zero almost surely, replacing its time-zero value by the constant zero yields a process agreeing with the original simultaneously at all nonnegative times almost surely. The modified process has the exact pointwise-zero start required by the published IsLevyProcess predicate.
-- source:
--   Kyprianou (2006), Chapter 6 real Lévy-process initial condition; normalisation bridge to the pointwise-zero LeanLevy interface.

import Mathlib

set_option autoImplicit false
open MeasureTheory
open scoped NNReal

theorem Kyprianou.Ch06.zeroTimeNormalisationAeEq
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0) :
    ∀ᵐ ω ∂P, ∀ t : NNReal,
      (if t = 0 then (0 : Real) else X t ω) = X t ω := by sorry
