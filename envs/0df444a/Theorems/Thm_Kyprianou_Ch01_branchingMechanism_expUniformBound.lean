-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingMechanism_expUniformBound
-- name    : Kyprianou.Ch01.branchingMechanism_expUniformBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T18:07:27.818939+00:00
-- url     : https://prove2.me/theorems/df90ee03-ebb9-4c82-ac7c-318285c1739e
-- title:
--   Uniform exponential-factor bound for nonnegative Laplace arguments
-- statement:
--   The branching mechanism exponential factor is uniformly bounded by 1+exp(b), independently of the offspring count k, whenever the Laplace parameter y lies between zero and b.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(iii), branching mechanism convergence and continuity

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingMechanism_expUniformBound
    (b : ℝ) (hb : 0 ≤ b) (k : ℕ) (y : ℝ)
    (hy0 : 0 ≤ y) (hyb : y ≤ b) :
    |1 - Real.exp (-y * ((k : ℝ) - 1))| ≤ 1 + Real.exp b := by sorry
