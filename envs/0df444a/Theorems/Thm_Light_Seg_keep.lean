-- Prove2me | Theorems.Thm_Light_Seg_keep
-- name    : Light.Seg.keep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:26:18.426416+00:00
-- url     : https://prove2.me/theorems/db8ef6df-be34-4f87-bc28-7414032187db
-- title:
--   Seg: keep
-- statement:
--   A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
--   `h.keep` carries `h` to a later memory across the steps whose promises are in the context.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L109-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L109-L111

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

theorem Light.Seg.keep (h : Seg μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_10507305537187907905 hx_p2m_10507305537187907905
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_4247050351032278221);
                  (try have := h_p2m_4247050351032278221 x_p2m_10507305537187907905 (by omega));
                  revert h_p2m_4247050351032278221)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_10507305537187907905;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_4856426279979274271);
                  (try have := h_p2m_4856426279979274271 x_p2m_10507305537187907905 (by omega));
                  revert h_p2m_4856426279979274271)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_12566650714491517558);
                  (try have := h_p2m_12566650714491517558 x_p2m_10507305537187907905 (by omega));
                  revert h_p2m_12566650714491517558)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))) :
    Seg μ' a l := by sorry
