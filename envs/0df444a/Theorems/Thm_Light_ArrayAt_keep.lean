-- Prove2me | Theorems.Thm_Light_ArrayAt_keep
-- name    : Light.ArrayAt.keep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:13.158908+00:00
-- url     : https://prove2.me/theorems/d603d4d8-07af-4181-9535-b8281cbe87e3
-- title:
--   Array At: keep
-- statement:
--   An array stays in place when its cells do not change.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L81-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L81-L84

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ArrayAt

theorem Light.ArrayAt.keep (h : ArrayAt μ a l N U top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_9451296152311787892 hx_p2m_9451296152311787892
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_9798918632343803250);
                  (try have := h_p2m_9798918632343803250 x_p2m_9451296152311787892 (by omega));
                  revert h_p2m_9798918632343803250)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_9451296152311787892;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_1958473802920672966);
                  (try have := h_p2m_1958473802920672966 x_p2m_9451296152311787892 (by omega));
                  revert h_p2m_1958473802920672966)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_17028183595724192009);
                  (try have := h_p2m_17028183595724192009 x_p2m_9451296152311787892 (by omega));
                  revert h_p2m_17028183595724192009)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))) :
    ArrayAt μ' a l N U top := by sorry
