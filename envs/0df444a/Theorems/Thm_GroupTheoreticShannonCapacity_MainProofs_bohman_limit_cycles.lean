-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_bohman_limit_cycles
-- name    : GroupTheoreticShannonCapacity.MainProofs.bohman_limit_cycles
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:37:21.394797+00:00
-- url     : https://prove2.me/theorems/d74760c0-dc00-4758-b295-870b5f85fa8d
-- title:
--   Main Proofs: bohman limit cycles
-- statement:
--   Bohman limit for cycle graphs C_p.
--
--   Since C_p ≃g E_{p/2}, this follows from `bohman_limit_fractionGraph_two`
--   via the isomorphism `cycleGraph_iso_fractionGraph_two`.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L1096-L1109
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L1096-L1109

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.bohman_limit_cycles :
    ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N,
      |(p : ℝ) / 2 - shannonCapacity (SimpleGraph.cycleGraph p)| < ε := by sorry
