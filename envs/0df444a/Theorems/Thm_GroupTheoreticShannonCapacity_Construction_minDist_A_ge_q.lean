-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_minDist_A_ge_q
-- name    : GroupTheoreticShannonCapacity.Construction.minDist_A_ge_q
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:33:55.793278+00:00
-- url     : https://prove2.me/theorems/d52eb593-e06a-468d-81e6-dbeb1d765c07
-- title:
--   Construction: min Dist A ge q
-- statement:
--   (i) λ_∞(L(A)) ≥ q (Theorem 3.12(i), th:main-constr)
--
--       The lattice L(A) has minimum distance at least q, where A = X + q•I
--       and X is a P₀-matrix. This follows from the general P₀ bound.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1021-L1037
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1021-L1037

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.minDist_A_ge_q (n : ℕ) [NeZero n] (k b r s : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hrb : r ≤ b) :
    Lattice.minDistance n (Lattice.latticeOfMatrix n
      ((matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ))) ≥
      (q n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) := by sorry
