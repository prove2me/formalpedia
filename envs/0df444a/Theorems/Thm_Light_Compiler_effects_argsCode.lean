-- Prove2me | Theorems.Thm_Light_Compiler_effects_argsCode
-- name    : Light.Compiler.effects_argsCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:31.073906+00:00
-- url     : https://prove2.me/theorems/cd104cab-fcb3-4d61-81b6-fcb176e712be
-- title:
--   Compiler: effects args Code
-- statement:
--   The code of the arguments leaves their values in T_k, T_{k+1}, … and changes nothing but ADDR
--   and the temporaries from T_k on.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/CallFrames.lean#L38-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/CallFrames.lean#L38-L58

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

theorem Light.Compiler.effects_argsCode (I : Framed Z σ q m) (es : List Expr) (k : ℕ)
    (hw : ∀ e ∈ es, e.width ≤ Z.F) (hs : ∀ e ∈ es, e.Safe Z.lim σ)
    (hk : k + es.length ≤ Z.F + 1) :
    (∀ i < es.length,
        effects (argsCode es k) m (cT (k + i)) = wd W (frame (es.map (·.val σ)) i)) ∧
      AgreeOutside (Temps k Z.F) m (effects (argsCode es k) m) := by sorry
