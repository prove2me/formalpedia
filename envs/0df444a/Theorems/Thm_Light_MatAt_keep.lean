-- Prove2me | Theorems.Thm_Light_MatAt_keep
-- name    : Light.MatAt.keep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:34:52.252106+00:00
-- url     : https://prove2.me/theorems/079b9ba0-ee2d-42fb-a898-238248444b89
-- title:
--   Mat At: keep
-- statement:
--   A matrix stays where it is if its cells do not change.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L211-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L211-L213

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

theorem Light.MatAt.keep {n k : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (hs : SameOn (Inside a (n * k)) μ μ' := by
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
    MatAt μ' a A := by sorry
