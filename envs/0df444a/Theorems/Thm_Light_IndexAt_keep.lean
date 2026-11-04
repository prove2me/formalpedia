-- Prove2me | Theorems.Thm_Light_IndexAt_keep
-- name    : Light.IndexAt.keep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:16.14714+00:00
-- url     : https://prove2.me/theorems/a6c820be-a8c5-444a-8ff7-2abe59f1b8bf
-- title:
--   Index At: keep
-- statement:
--   A list of natural numbers stays in place when its cells do not change.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L120-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L120-L128

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
open Light.IndexAt
variable {l : List ℕ} {p : ℕ}

theorem Light.IndexAt.keep (h : IndexAt μ a l N p top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_9798918632343803250 hx_p2m_9798918632343803250
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_18012199293970436122);
                  (try have := h_p2m_18012199293970436122 x_p2m_9798918632343803250 (by omega));
                  revert h_p2m_18012199293970436122)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_9798918632343803250;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_16332825214033116840);
                  (try have := h_p2m_16332825214033116840 x_p2m_9798918632343803250 (by omega));
                  revert h_p2m_16332825214033116840)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_16325795306354567673);
                  (try have := h_p2m_16325795306354567673 x_p2m_9798918632343803250 (by omega));
                  revert h_p2m_16325795306354567673)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))) :
    IndexAt μ' a l N p top := by sorry
