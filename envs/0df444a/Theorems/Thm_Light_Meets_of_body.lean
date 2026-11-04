-- Prove2me | Theorems.Thm_Light_Meets_of_body
-- name    : Light.Meets.of_body
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:33:07.274746+00:00
-- url     : https://prove2.me/theorems/d351f94e-6561-49b1-87bf-b52715100498
-- title:
--   Meets: of body
-- statement:
--   From a theorem about a body to the specification.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Calls.lean#L49-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Calls.lean#L49-L53

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

theorem Light.Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q := by sorry
