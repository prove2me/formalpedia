-- Prove2me | Theorems.Thm_Light_TriInst_Pre_keep
-- name    : Light.TriInst.Pre.keep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:42.192781+00:00
-- url     : https://prove2.me/theorems/dc47202c-c77d-4356-abf9-52927891740e
-- title:
--   Pre: keep
-- statement:
--   An instance stays where it is if no cell below the free pointer changes.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Programs/Tasks.lean#L66-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Programs/Tasks.lean#L66-L69

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Theorems.Thm_Light_ArrayAt_keep
import Theorems.Thm_Light_IndexAt_keep
import Theorems.Thm_Light_ListAt_keep
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
set_option autoImplicit false
section
open ThreeSumApsp
open Light
open ThreeSumApsp.Spec

theorem Light.TriInst.Pre.keep {x : TriInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr)
    (hs : Kept μ μ' fr := by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_13852537352074534653 hx_p2m_13852537352074534653
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_10507305537187907905);
                  (try have := h_p2m_10507305537187907905 x_p2m_13852537352074534653 (by omega));
                  revert h_p2m_10507305537187907905)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_13852537352074534653;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_17167928071560346525);
                  (try have := h_p2m_17167928071560346525 x_p2m_13852537352074534653 (by omega));
                  revert h_p2m_17167928071560346525)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_10331794896191121659);
                  (try have := h_p2m_10331794896191121659 x_p2m_13852537352074534653 (by omega));
                  revert h_p2m_10331794896191121659)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))) :
    x.Pre μ' fr := by sorry
