-- Prove2me | Theorems.Thm_Light_SameOn_mono
-- name    : Light.SameOn.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:47.211645+00:00
-- url     : https://prove2.me/theorems/7ea92cc9-aadd-467c-b1ad-a8f649320e18
-- title:
--   Same On: mono
-- statement:
--   Fewer cells are kept.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L106-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L106-L107

module
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
set_option autoImplicit false
public section
open Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}

theorem Light.SameOn.mono (h : SameOn K μ μ') (hK : ∀ b, K' b → K b) : SameOn K' μ μ' := by sorry
