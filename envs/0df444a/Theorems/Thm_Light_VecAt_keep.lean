-- Prove2me | Theorems.Thm_Light_VecAt_keep
-- name    : Light.VecAt.keep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:35:12.505603+00:00
-- url     : https://prove2.me/theorems/e2a44fe8-ee91-4779-8530-d6c8da4078fe
-- title:
--   Vec At: keep
-- statement:
--   A vector of indices stays where it is if its cells do not change.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L231-L233
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L231-L233

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

theorem Light.VecAt.keep {t n : ℕ} {I : Fin t → Fin n} (h : VecAt μ a I)
    (hs : SameOn (Inside a t) μ μ' := by
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
    VecAt μ' a I := by sorry
