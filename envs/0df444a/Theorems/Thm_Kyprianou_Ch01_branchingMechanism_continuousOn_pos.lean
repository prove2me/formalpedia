-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingMechanism_continuousOn_pos
-- name    : Kyprianou.Ch01.branchingMechanism_continuousOn_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T18:06:08.303201+00:00
-- url     : https://prove2.me/theorems/afd4d309-e204-4252-b118-936732629edd
-- title:
--   Continuity of the offspring-PMF branching mechanism at every positive Laplace argument
-- statement:
--   For every real branching rate and every probability mass function on offspring counts, the mechanism lambda times the sum of p_k times (1-exp(-q(k-1))) is continuous in q strictly above zero. Local uniform convergence follows from bounding the exponential summands on each compact positive q interval by a common finite constant times the summable offspring probabilities. This provides the analytic continuity needed for the branching cumulant evolution equation.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(iii); dominated continuous offspring series

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingMechanism_continuousOn_pos (rate : ℝ) (offspring : PMF ℕ) :
    ContinuousOn (branchingMechanism rate offspring) (Ioi (0 : ℝ)) := by sorry
