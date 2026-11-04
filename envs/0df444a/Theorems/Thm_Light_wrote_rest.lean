-- Prove2me | Theorems.Thm_Light_wrote_rest
-- name    : Light.wrote_rest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:50.063615+00:00
-- url     : https://prove2.me/theorems/0bdfc225-f844-47e3-89d7-a4b65be5bc4a
-- title:
--   Light: wrote rest
-- statement:
--   A cell that has not been written (yet).
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L139-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L139-L141

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

theorem Light.wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by sorry
