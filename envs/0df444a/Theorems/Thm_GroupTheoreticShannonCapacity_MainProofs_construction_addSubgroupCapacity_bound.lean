-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_construction_addSubgroupCapacity_bound
-- name    : GroupTheoreticShannonCapacity.MainProofs.construction_addSubgroupCapacity_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:37:17.644874+00:00
-- url     : https://prove2.me/theorems/606bb885-db25-4739-8d64-a45bc2c85497
-- title:
--   Main Proofs: construction add Subgroup Capacity bound
-- statement:
--   Helper lemma: construction_lower_bound gives a lower bound on addSubgroupShannonCapacity.
--   This is extracted from subgroup_capacity_limit to reduce proof term size.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L599-L619
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L599-L619

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.construction_addSubgroupCapacity_bound (n : ℕ) [NeZero n] (k b r s : ℕ)
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hrb : r ≤ b) :
    let p' := Construction.p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    let q' := Construction.q n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    ∃ (p'' q'' : ℕ) (_ : NeZero p'') (_ : 0 < q''),
      (p'' : ℚ) = p' ∧ (q'' : ℚ) = q' ∧
      addSubgroupShannonCapacity (fractionGraph p'' q'') ≥ (p'' : ℝ) ^ (1 / (n : ℝ)) := by sorry
