-- Prove2me | Theorems.Thm_Light_Ends_pieceToThen
-- name    : Light.Ends.pieceToThen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:32:05.185837+00:00
-- url     : https://prove2.me/theorems/7edafb4d-e873-453a-bdc3-915d6d50c741
-- title:
--   Ends: piece To Then
-- statement:
--   **A piece of text that assigns only the locals `xs`**, followed by the rest of the program,
--   which gets the steps that are left.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L335-L340
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L335-L340

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}

theorem Light.Ends.pieceToThen (xs : List ℕ) (h : Ends lim P d s₁ ⟨frame l, μ⟩ T₁ R)
    (rest : ∀ loc' μ', R ⟨loc', μ'⟩ → Ends lim P d s₂ ⟨frame (refreshLocals l loc' xs), μ'⟩ (T - T₁) Q)
    (hxs : s₁.assigns ⊆ xs := by simp)
    (hT : T₁ ≤ T := by
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
    Ends lim P d (_root_.Light.Stmt.seq s₁ s₂) ⟨frame l, μ⟩ T Q := by sorry
