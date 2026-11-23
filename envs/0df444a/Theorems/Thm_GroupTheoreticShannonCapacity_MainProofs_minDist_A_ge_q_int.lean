-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_minDist_A_ge_q_int
-- name    : GroupTheoreticShannonCapacity.MainProofs.minDist_A_ge_q_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:36:53.055319+00:00
-- url     : https://prove2.me/theorems/96f938e7-05a7-4eeb-b3b4-d859fbdb8630
-- title:
--   Main Proofs: min Dist A ge q int
-- statement:
--   The minimum distance bound using integer matrix.
--
--   Proof: The lattices L(A') and L(matrixA) are equal when mapped to ℝ:
--   - L(A') = {A'x : x ∈ ℤ^n} mapped via ℤ → ℝ
--   - L(matrixA) = {(matrixA)x : x ∈ ℤ^n} mapped via ℚ → ℝ
--   Since A' maps to matrixA under ℤ → ℚ, these coincide under ℤ → ℚ → ℝ = ℤ → ℝ.
--   Then apply Construction.minDist_A_ge_q.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L242-L262
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L242-L262

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.minDist_A_ge_q_int (n : ℕ) [NeZero n] (k b r s : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hrb : r ≤ b)
    (A' : Matrix (Fin n) (Fin n) ℤ) (q' : ℕ)
    (hA : matrixA n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = A'.map (↑· : ℤ → ℚ))
    (hq : (q' : ℚ) = Construction.q n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)) :
    minDistance n (latticeOfMatrix n (A'.map (↑· : ℤ → ℝ))) ≥ q' := by sorry
