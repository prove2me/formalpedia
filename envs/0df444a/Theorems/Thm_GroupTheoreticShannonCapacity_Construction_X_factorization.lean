-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_X_factorization
-- name    : GroupTheoreticShannonCapacity.Construction.X_factorization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:27:15.8728+00:00
-- url     : https://prove2.me/theorems/2bcc1370-9223-469c-a26d-87e03bd106cb
-- title:
--   Construction: X factorization
-- statement:
--   X factorization: for s ≠ 0, X = (ka^{n-1}/s) · D_{s/a} · M_α · D_{a/s}
--       where α = (rs^n)/(ka^n)
--
--       Proof outline:
--       1. The matrix product (D_{s/a} · M_α · D_{a/s})_{i,j} = (s/a)^i · M_α(i,j) · (a/s)^j
--       2. For i < j (upper triangular): M_α(i,j) = α = rs^n/(ka^n)
--          So entry = (s/a)^i · (rs^n/(ka^n)) · (a/s)^j = r·s^(i+n-j)·a^(j-i-n)/(k·a^n)
--          Multiplied by scalar k·a^(n-1)/s gives r·a^(j-i-1)·s^(n-(j-i+1)) ✓
--       3. For i > j (lower triangular): M_α(i,j) = -1
--          So entry = -(s/a)^i · (a/s)^j = -s^(i-j)/a^(i-j)
--          Multiplied by scalar gives -k·a^(n-(i-j+1))·s^(i-j-1) ✓
--       4. For i = j (diagonal): M_α(i,j) = 0, so both sides are 0 ✓
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L550-L598
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L550-L598

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.X_factorization (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hs : s ≠ 0) :
    let α : ℝ := (r : ℝ) * s^n / (k * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n)
    let a' : ℝ := a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)
    let scalar : ℝ := k * a'^(n-1) / s
    (matrixX n k b r s).map (↑· : ℚ → ℝ) =
      scalar • (diagPow n (s/a') * MAlpha.Mα n α * diagPow n (a'/s)) := by sorry
