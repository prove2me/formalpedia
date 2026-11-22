-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingSemigroupEqOfOneAncestor
-- name    : Kyprianou.Ch01.branchingSemigroupEqOfOneAncestor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:36:13.451737+00:00
-- url     : https://prove2.me/theorems/84c43375-1593-4da6-b384-481dc84088f3
-- title:
--   Branching convolution determines every population law from the one-ancestor law
-- statement:
--   For two branching probability-mass-function families with identical one-ancestor law at every time, show that their complete population laws agree. Use the already Proved branchingZeroAbsorbing for initial population zero, then induct on initial population using the exact branching convolution identity. This is a concrete algebraic child of the reverse Lamperti generator-uniqueness theorem, to be attached to its accepted parent sketch.
-- source:
--   Kyprianou Ch1 Definition 1.14, main reverse Lamperti root ac1b29c6-5525-4344-a03d-7469824736ed, uniqueness parent abf1b453-26bc-421b-b350-3ce810bb8479.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingSemigroupEqOfOneAncestor
    (K₁ K₂ : PopulationLaws)
    (hBranch₁ : HasBranchingProperty K₁)
    (hBranch₂ : HasBranchingProperty K₂)
    (hOne : ∀ t : ℝ≥0, K₁ 1 t = K₂ 1 t) :
    K₁ = K₂ := by
  sorry
