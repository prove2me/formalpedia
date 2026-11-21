-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_noCross_beforeFiniteV1
-- name    : Kyprianou.Ch01.firstUpperPassage_noCross_beforeFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:56:28.944912+00:00
-- url     : https://prove2.me/theorems/b31ee262-2d59-44eb-a533-5328655b4ec4
-- title:
--   A finite strict first-passage has no earlier strict barrier crossing
-- statement:
--   For any path starting at or below a barrier s, if its first strictly upper passage is finite at τ, no time t<τ can satisfy X_t>s. The t=0 case follows from the initial bound. For t>0, a strict crossing contradicts the already Proved firstUpperPassage_le_of_strict_crossingV1, which puts the first passage at or before t. This is the exact deterministic no-early-crossing half of the continuity-based barrier-contact and strong-Markov passage-restart identities.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, basic first-upper-passage minimality.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassage_noCross_beforeFiniteV1
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω)
    (hInitial : X 0 ω ≤ s) (τ : ℝ≥0)
    (hPass : firstUpperPassage X s ω = (τ : WithTop ℝ≥0)) :
    ∀ t : ℝ≥0, t < τ → X t ω ≤ s := by sorry
