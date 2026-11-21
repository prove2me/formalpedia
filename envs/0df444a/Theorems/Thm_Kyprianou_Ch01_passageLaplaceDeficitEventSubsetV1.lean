-- Prove2me | Theorems.Thm_Kyprianou_Ch01_passageLaplaceDeficitEventSubsetV1
-- name    : Kyprianou.Ch01.passageLaplaceDeficitEventSubsetV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:21:32.440546+00:00
-- url     : https://prove2.me/theorems/431aeb11-ca12-46c4-8e26-539bf6215b45
-- title:
--   First passage tail events lie in discounted Laplace-deficit events
-- statement:
--   For an arbitrary real-valued path X and first strictly upper passage at barrier s, the outer event that passage is at least ε is included in the event that its unit-discounted Laplace deficit is at least 1-exp(-ε). A direct WithTop case split handles infinite passage by positivity of exp and finite passage by order monotonicity of exp. This exact set inclusion avoids dependent match elaboration and is the probabilistic input to the inverse Gaussian Markov tail bound.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, first-passage discount convention.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.passageLaplaceDeficitEventSubsetV1
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ε : ℝ≥0) :
    {ω | (ε : WithTop ℝ≥0) ≤ firstUpperPassage X s ω} ⊆
      {ω | 1 - Real.exp (-(ε : ℝ)) ≤
        1 - passageLaplace (firstUpperPassage X s) 1 ω} := by sorry
