-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_det_B_eq_p_int
-- name    : GroupTheoreticShannonCapacity.MainProofs.det_B_eq_p_int
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:36:58.38007+00:00
-- url     : https://prove2.me/theorems/59d839ec-6fed-4b91-bf42-41e37ad9c2a9
-- title:
--   Main Proofs: det B eq p int
-- statement:
--   det(B') = p' for the integer matrices.
--
--   Proof: From Construction.det_B_eq_p we have (matrixB).det = p over ℚ.
--   Since B = B'.map, we have (B'.map).det = (B'.det).map = p.
--   Since p = p' ∈ ℕ ⊆ ℤ ⊆ ℚ, we get B'.det = p' by injectivity.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L269-L285
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean#L269-L285

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice

theorem GroupTheoreticShannonCapacity.MainProofs.det_B_eq_p_int (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (B' : Matrix (Fin n) (Fin n) ℤ) (p' : ℕ)
    (hB : matrixB n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = B'.map (↑· : ℤ → ℚ))
    (hp : (p' : ℚ) = Construction.p n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)) :
    B'.det = p' := by sorry
