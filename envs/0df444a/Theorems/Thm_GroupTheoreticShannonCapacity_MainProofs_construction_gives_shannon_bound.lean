-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_construction_gives_shannon_bound
-- name    : GroupTheoreticShannonCapacity.MainProofs.construction_gives_shannon_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:37:07.650133+00:00
-- url     : https://prove2.me/theorems/c737a596-71f3-48e2-b4b3-1b2fa481c20f
-- title:
--   Main Proofs: construction gives shannon bound
-- statement:
--   The construction produces an independent set in E_{p/q}^⊠n of size ≥ p,
--   giving a lower bound on Shannon capacity Θ(E_{p/q}) ≥ p^(1/n).
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L357-L384
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L357-L384

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.construction_gives_shannon_bound (n k b r s : ℕ) [NeZero n] (hk : 1 ≤ k)
    (hb : 1 ≤ b) (hrb : r ≤ b) :
    let pVal := Construction.p n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)
    let qVal := Construction.q n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)
    ∃ (p' q' : ℕ) (_ : NeZero p') (_ : 0 < q'),
      (p' : ℚ) = pVal ∧ (q' : ℚ) = qVal ∧
      shannonCapacity (fractionGraph p' q') ≥ (p' : ℝ) ^ (1 / (n : ℝ)) := by sorry
