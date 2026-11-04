-- Prove2me | Theorems.Thm_Light_seg_wrote_map
-- name    : Light.seg_wrote_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:36:10.242285+00:00
-- url     : https://prove2.me/theorems/f3291770-bfd3-4aba-b5f0-30deff8deb73
-- title:
--   Light: seg wrote map
-- statement:
--   A pass that writes g of the entries of a list leaves the list mapped by g.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Pass.lean#L38-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Pass.lean#L38-L41

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Pass
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

theorem Light.seg_wrote_map (g : ℤ → ℤ) (L : List ℤ) :
    Seg (wrote μ dst (fun i => g (L.getD i 0)) L.length) dst (L.map g) := by sorry
