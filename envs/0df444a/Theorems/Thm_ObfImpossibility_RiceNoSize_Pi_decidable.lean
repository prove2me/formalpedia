-- Prove2me | Theorems.Thm_ObfImpossibility_RiceNoSize_Pi_decidable
-- name    : ObfImpossibility.RiceNoSize.Pi_decidable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:57.913801+00:00
-- url     : https://prove2.me/theorems/8e303a5b-8bf0-47eb-831e-10e95f4b805b
-- title:
--   Proof of Thm A.4, p. A:42 — $\Pi$ is decidable
-- statement:
--   The promise problem $\Pi=(\Pi_Y,\Pi_N)$ of the proof of Theorem A.4 is decidable: there is a program $T$, run on canonical descriptions $\ulcorner M\urcorner$ of machines, such that
--   $$M\in\Pi_Y\Rightarrow T(\ulcorner M\urcorner)=1,\qquad M\in\Pi_N\Rightarrow T(\ulcorner M\urcorner)=0.$$
--   Outside $\Pi_Y\cup\Pi_N$ nothing is required of $T$; it may diverge.
--
--   This is the second property that makes $\Pi$ an instance of the hypothesis of Conjecture A.3. The paper's $T$ runs $M$ on every input $x<|M|$ and outputs $1$ exactly when some answer is non-zero.
--
--   **Formalization Note** $T$ is a Mathlib `Nat.Partrec.Code` applied to the natural-number description of $M$, so decidability means decidability by a partial recursive function.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:42, proof of Theorem A.4 ("We claim that Π is decidable.")

import Mathlib
import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects

namespace ObfImpossibility.RiceNoSize

/-- p. A:42: the promise problem `Π = (Π_Y, Π_N)` of the proof of Theorem A.4 is decidable:
some program `T`, run on descriptions `⌜M⌝`, outputs `1` on `Π_Y` and `0` on `Π_N`. -/
theorem Pi_decidable : ∃ T : Nat.Partrec.Code, Decides T PiY PiN := by sorry

end ObfImpossibility.RiceNoSize
