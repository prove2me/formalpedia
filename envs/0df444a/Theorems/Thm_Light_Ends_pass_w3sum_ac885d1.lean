-- Prove2me | Theorems.Thm_Light_Ends_pass_w3sum_ac885d1
-- name    : Light.Ends.pass_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:36:14.818188+00:00
-- url     : https://prove2.me/theorems/ea6d5eb4-172b-48d5-8919-f9bf02c6141e
-- title:
--   Ends: pass
-- statement:
--   **The rule for a pass.**  The locals x and y hold the length n and the address dst.  In round j
--   the locals are the given ones with j in the counter, and the memory is `wrote μ dst f j`; there the
--   expression e has to be safe and have the value f j.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Pass.lean#L46-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Pass.lean#L46-L69

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Pass
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

theorem Light.Ends.pass_w3sum_ac885d1 {c x y n T : ℕ} {e : Expr} {loc : ℕ → ℤ} {Q : State → Prop} (f : ℕ → ℤ)
    (round :
      ∀ j < n,
        e.Safe lim ⟨Function.update loc c j, wrote μ dst f j⟩ ∧ e.val ⟨Function.update loc c j, wrote μ dst f j⟩ = f j)
    (done : Q ⟨Function.update loc c n, wrote μ dst f n⟩) (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space)
    (hlen : loc x = n) (haddr : loc y = dst) (hx : x ≠ c := by decide) (hy : y ≠ c := by decide)
    (hT : n * (e.cost + 12) + 6 ≤ T := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega))) :
    Ends lim P d (pass c (v x) (v y) e) ⟨loc, μ⟩ T Q := by sorry
