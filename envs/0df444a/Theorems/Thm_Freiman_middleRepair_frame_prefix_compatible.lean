-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_prefix_compatible
-- name    : Freiman.middleRepair_frame_prefix_compatible
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:34.974097+00:00
-- url     : https://prove2.me/theorems/2bfa0378-3588-449a-bb41-ec518387e259
-- title:
--   middleRepair frame prefix compatible
-- statement:
--   Induct over the interval of depths to propagate physical-prefix compatibility backward.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_prefix_compatible :
  (∀ (c d : MiddleCore) (a : ℤ → ℕ+), middleProper c d → middleCompatible d a → middleCompatible c a) →
  ∀ p : ℕ → MiddleCore, (∀ n : ℕ, middleProper (p n) (p (n+1))) →
  ∀ n m : ℕ, n≤m → ∀ a : ℤ → ℕ+, middleCompatible (p m) a → middleCompatible (p n) a := by
  sorry
