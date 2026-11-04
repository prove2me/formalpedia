-- Prove2me | Theorems.Thm_Light_Ends_pieceTo
-- name    : Light.Ends.pieceTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:31:58.992085+00:00
-- url     : https://prove2.me/theorems/aa892d27-914d-478a-81c0-bdaef43d060f
-- title:
--   Ends: piece To
-- statement:
--   **A piece of text that assigns only the locals `xs`**, at the end of the program.  `h` is the
--   lemma about the piece.  Afterwards the locals are the list `l` with the entries `xs` read from the
--   locals `loc'` of which the lemma speaks.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L323-L331
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L323-L331

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

theorem Light.Ends.pieceTo (xs : List ℕ) (h : Ends lim P d s ⟨frame l, μ⟩ T₁ R)
    (done : ∀ loc' μ', R ⟨loc', μ'⟩ → Q ⟨frame (refreshLocals l loc' xs), μ'⟩) (hxs : s.assigns ⊆ xs := by simp)
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
    Ends lim P d s ⟨frame l, μ⟩ T Q := by sorry
