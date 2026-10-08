-- Prove2me | Theorems.Thm_ObfImpossibility_RiceSimulator_stage_answer_sound
-- name    : ObfImpossibility.RiceSimulator.stage_answer_sound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:55.332709+00:00
-- url     : https://prove2.me/theorems/eb827d4e-4e64-47b9-957c-7c8eeb2adb76
-- title:
--   p. A:41 — if the simulator halts, it returns the same answer as $T(M)$
-- statement:
--   Let $T$ and $M$ be machines, $n\in\mathbb N$ and $\sigma\in\mathbb N$. Suppose stage $n$ of the simulator stops with answer $\sigma$, that is, $T$ run for $n$ steps halts on every machine of $S_n$ (the machines of size $|M|$ that are $n$-compatible with $M$) with output $\sigma$. Then
--   $$T(\ulcorner M\urcorner)=\sigma .$$
--
--   Since $M$ is $n$-compatible with itself, $M$ always belongs to $S_n$; so whatever stage the simulator stops at, its answer is the one $T$ gives on $M$. This is the correctness half of the proof of Theorem A.2.
--
--   **Formalization Note** "Run $T$ for $n$ steps" is `Code.evaln n T`; the conclusion is `σ ∈ Code.eval T (encode M)`, i.e. $T$ halts on $\ulcorner M\urcorner$ with output $\sigma$. No promise hypothesis is needed.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:41, proof of Theorem A.2

import Mathlib
import Definitions.Def_ObfImpossibility_RiceSimulator_Setting

namespace ObfImpossibility.RiceSimulator

/-- p. A:41: if the simulator halts (at some stage `n` with answer `σ`) then it returns the
same answer as `T(M)`. -/
theorem stage_answer_sound (T M : Machine) (n σ : ℕ) (h : StageAnswer T M n σ) :
    σ ∈ T.eval (Encodable.encode M) := by sorry

end ObfImpossibility.RiceSimulator
