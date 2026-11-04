-- Prove2me | Theorems.Thm_Light_SegN_keep
-- name    : Light.SegN.keep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:34:29.205839+00:00
-- url     : https://prove2.me/theorems/0a8fe36e-d3e5-4b3a-8910-80e07538dafe
-- title:
--   Seg N: keep
-- statement:
--   A segment of natural numbers stays where it is if its cells do not change.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L190-L192
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L190-L192

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
set_option autoImplicit false
public section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

theorem Light.SegN.keep {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_9771269342517545196 hx_p2m_9771269342517545196
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_8345441044875591925);
                  (try have := h_p2m_8345441044875591925 x_p2m_9771269342517545196 (by omega));
                  revert h_p2m_8345441044875591925)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_9771269342517545196;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_18012199293970436122);
                  (try have := h_p2m_18012199293970436122 x_p2m_9771269342517545196 (by omega));
                  revert h_p2m_18012199293970436122)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_16332825214033116840);
                  (try have := h_p2m_16332825214033116840 x_p2m_9771269342517545196 (by omega));
                  revert h_p2m_16332825214033116840)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))) :
    SegN μ' a l := by sorry
