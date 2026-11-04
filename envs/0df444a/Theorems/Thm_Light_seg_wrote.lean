-- Prove2me | Theorems.Thm_Light_seg_wrote
-- name    : Light.seg_wrote
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:36:11.212767+00:00
-- url     : https://prove2.me/theorems/909f70ae-3a9c-49ad-a40d-f0608b54696d
-- title:
--   Light: seg wrote
-- statement:
--   After the pass the n cells hold the list of the values f 0, …, f (n - 1).
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Pass.lean#L33-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Pass.lean#L33-L35

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Pass
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

theorem Light.seg_wrote {n : ℕ} {l : List ℤ} (hl : l.length = n)
    (h : ∀ i (hi : i < l.length), l[i] = f i) : Seg (wrote μ dst f n) dst l := by sorry
