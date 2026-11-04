-- Prove2me | Theorems.Thm_Light_SameOn_refl
-- name    : Light.SameOn.refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:46.786863+00:00
-- url     : https://prove2.me/theorems/bbfade68-611f-4647-95cb-cbb275358644
-- title:
--   Same On: refl
-- statement:
--   The Same On construction uses the refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L100-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L100-L100

module
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
set_option autoImplicit false
public section
open Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}

theorem Light.SameOn.refl : SameOn K μ μ := by sorry
