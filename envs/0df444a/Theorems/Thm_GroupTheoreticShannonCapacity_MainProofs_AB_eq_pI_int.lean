-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_AB_eq_pI_int
-- name    : GroupTheoreticShannonCapacity.MainProofs.AB_eq_pI_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:36:38.431803+00:00
-- url     : https://prove2.me/theorems/79c17a6f-feaf-459f-afaa-cb7274b7cdb1
-- title:
--   Main Proofs: AB eq p I int
-- statement:
--   The integer version of AB = pI.
--
--   Proof: From Construction.AB_eq_pI we have matrixA * matrixB = p • 1 over ℚ.
--   Since A = A'.map and B = B'.map and p = p', this equation over ℚ implies
--   A' * B' = p' • 1 over ℤ by injectivity of the ring homomorphism ℤ → ℚ.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L207-L233
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L207-L233

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.AB_eq_pI_int (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (A' : Matrix (Fin n) (Fin n) ℤ) (B' : Matrix (Fin n) (Fin n) ℤ) (p' : ℕ)
    (hA : matrixA n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = A'.map (↑· : ℤ → ℚ))
    (hB : matrixB n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = B'.map (↑· : ℤ → ℚ))
    (hp : (p' : ℚ) = Construction.p n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)) :
    A' * B' = p' • 1 := by sorry
