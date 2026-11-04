-- Prove2me | Theorems.Thm_Light_Compiler_effects_newFrame
-- name    : Light.Compiler.effects_newFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:49.025505+00:00
-- url     : https://prove2.me/theorems/8a7fde81-77f4-4f7c-a262-2d416bbe4621
-- title:
--   Compiler: effects new Frame
-- statement:
--   The new frame.  If T₀, T₁, … hold the values of the arguments, then afterwards the memory
--   represents the state in which the procedure starts, in the frame q + F + 1, and the stack cell
--   before that frame holds the position to return to.  Of the stack, only cells from q + F on have
--   changed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/CallFrames.lean#L104-L149
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/CallFrames.lean#L104-L149

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

theorem Light.Compiler.effects_newFrame (I : Framed Z σ q m) (hQ : q + Z.F + 1 + Z.F ≤ Z.Q) (args : List Expr)
    (hargs : ∀ i < args.length, m (cT i) = wd W (frame (args.map (·.val σ)) i)) {ret : ℕ}
    (hret : ret ≤ Z.disp) :
    Rel Z ⟨frame (args.map (·.val σ)), σ.mem⟩ (q + Z.F + 1)
        (effects (newFrame Z.F args.length ret) m) ∧
      effects (newFrame Z.F args.length ret) m (cStack (q + Z.F)) = wd W ret ∧
      AgreeOutside (Writable Z (q + Z.F)) m (effects (newFrame Z.F args.length ret) m) := by sorry
