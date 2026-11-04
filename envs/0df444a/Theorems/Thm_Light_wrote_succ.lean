-- Prove2me | Theorems.Thm_Light_wrote_succ
-- name    : Light.wrote_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:52.452455+00:00
-- url     : https://prove2.me/theorems/e0a4a5b5-e9f2-4918-aef7-b90ffdab8481
-- title:
--   Light: wrote succ
-- statement:
--   One more cell is written.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L144-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L144-L153

module
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
set_option autoImplicit false
public section
open Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}
variable {dst j : ℕ} {f : ℕ → ℤ}

theorem Light.wrote_succ : Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by sorry
