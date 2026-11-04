-- Prove2me | Theorems.Thm_Light_wrote_done
-- name    : Light.wrote_done
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:49.312288+00:00
-- url     : https://prove2.me/theorems/ac255a60-9da8-47ed-a6dd-0aea183d408c
-- title:
--   Light: wrote done
-- statement:
--   A cell that has been written.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L134-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L134-L136

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

theorem Light.wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by sorry
