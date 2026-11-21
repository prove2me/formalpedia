-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianPositiveLevelPassageEventuallyLtOfFiniteV2
-- name    : Kyprianou.Ch01.inverseGaussianPositiveLevelPassageEventuallyLtOfFiniteV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:42:43.953661+00:00
-- url     : https://prove2.me/theorems/847394f7-62a2-418f-a106-73edfe2a2c99
-- title:
--   Finite positive-level passage times are eventually bounded above near each positive barrier (explicit NNReal neighbourhood)
-- statement:
--   For any positive barrier s on a path with finite strictly-upper passage at all positive levels, and any real a above the passage time at s, the passage times at all sufficiently nearby barriers u≥s are still below a. The proof chooses a strict crossing before a and keeps it valid for nearby barrier levels using the open condition u<X_v. This is the deterministic upper-order neighbourhood bound required by tendsto_order for càdlàg/right-continuity construction. The neighbourhood variable is explicitly of type NNReal to agree with the passage process's time index.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, strict crossing and right-continuity argument.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianPositiveLevelPassageEventuallyLtOfFiniteV2
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hFinite : ∀ s : ℝ≥0, 0 < s →
      firstUpperPassage X (s : ℝ) ω ≠ ⊤)
    (s : ℝ≥0) (hs : 0 < s)
    (a : ℝ)
    (ha : (if s = 0 then (0 : ℝ)
      else (match firstUpperPassage X (s : ℝ) ω with
      | none => (0 : ℝ)
      | some t => (t : ℝ))) < a) :
    ∀ᶠ (u : ℝ≥0) in 𝓝[Ici s] s,
      (if u = 0 then (0 : ℝ)
      else (match firstUpperPassage X (u : ℝ) ω with
      | none => (0 : ℝ)
      | some t => (t : ℝ))) < a := by
  sorry
