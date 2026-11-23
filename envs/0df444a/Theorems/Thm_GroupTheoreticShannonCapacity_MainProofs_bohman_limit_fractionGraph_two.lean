-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_bohman_limit_fractionGraph_two
-- name    : GroupTheoreticShannonCapacity.MainProofs.bohman_limit_fractionGraph_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:08.57501+00:00
-- url     : https://prove2.me/theorems/a49a4cbe-53f8-4be2-93c9-ed242c87ecaf
-- title:
--   Main Proofs: bohman limit fraction Graph two
-- statement:
--   Bohman limit for fraction graphs E_{p/2}. This is the q=2 case of
--   `bohman_limit_fraction_graphs`.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L1071-L1090
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L1071-L1090

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.bohman_limit_fractionGraph_two :
    ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, [NeZero p] →
      |(p : ℝ) / 2 - shannonCapacity (fractionGraph p 2)| < ε := by sorry
