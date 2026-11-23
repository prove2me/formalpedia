-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_Y_factorization
-- name    : GroupTheoreticShannonCapacity.Construction.Y_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:49.052168+00:00
-- url     : https://prove2.me/theorems/ebf7070f-c4d5-4c5e-8535-1af1711cdcfe
-- title:
--   Construction: Y factorization
-- statement:
--   Y factorization: Y = -kb^{n-1} · D_{1/b} · M_α · D_b
--       where α = r/(kb^n)
--
--       Proof outline:
--       1. The matrix product (D_{1/b} · M_α · D_b)_{i,j} = (1/b)^i · M_α(i,j) · b^j
--       2. For i < j (upper triangular): M_α(i,j) = α = r/(kb^n)
--          So entry = (1/b)^i · (r/(kb^n)) · b^j = r·b^{j-i-n}
--          Multiplied by scalar -kb^{n-1} gives -r·b^{j-i-1} ✓
--       3. For i > j (lower triangular): M_α(i,j) = -1
--          So entry = -(1/b)^i · b^j = -b^{j-i}
--          Multiplied by scalar -kb^{n-1} gives k·b^{n-1+j-i} = k·b^{n-(i-j+1)} ✓
--       4. For i = j (diagonal): M_α(i,j) = 0, so both sides are 0 ✓
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L655-L686
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L655-L686

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.Y_factorization (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    let α : ℝ := (r : ℝ) / ((k : ℝ) * (b : ℝ)^n)
    let scalar : ℝ := -(k : ℝ) * (b : ℝ)^(n-1)
    (matrixY n k b r s).map (↑· : ℚ → ℝ) =
      scalar • (diagPow n (b : ℝ)⁻¹ * MAlpha.Mα n α * diagPow n (b : ℝ)) := by sorry
