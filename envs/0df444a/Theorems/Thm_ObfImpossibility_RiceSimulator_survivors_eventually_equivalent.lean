-- Prove2me | Theorems.Thm_ObfImpossibility_RiceSimulator_survivors_eventually_equivalent
-- name    : ObfImpossibility.RiceSimulator.survivors_eventually_equivalent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:03.778409+00:00
-- url     : https://prove2.me/theorems/d7e50c84-4bb4-4ea3-9492-b4f78d502bb5
-- title:
--   p. A:41 — for large $n$, every machine in $S_n$ is functionally equivalent to $M$
-- statement:
--   Let $M$ be a machine and, for $n\in\mathbb N$, let $S_n$ be the set of machines $N$ of size $|N|=|M|$ that are $n$-compatible with $M$. Then there is a number $n''$ such that
--   $$\forall n>n''\ \ \forall N\in S_n:\quad [N]\equiv[M].$$
--
--   Only finitely many machines have size $|M|$, and each one inequivalent to $M$ eventually leaves $S_n$ for good; the statement collects this into a single threshold. It is the step of the proof of Theorem A.2 that lets the simulator's answer stabilise on machines that $T$ must treat like $M$.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:41, proof of Theorem A.2 (paragraph "We claim that S always halts")

import Mathlib
import Definitions.Def_ObfImpossibility_RiceSimulator_Setting

namespace ObfImpossibility.RiceSimulator

/-- p. A:41 (proof of Theorem A.2): there is `n''` such that every machine `N ∈ S_n` with
`n > n''` satisfies `[N] ≡ [M]`. -/
theorem survivors_eventually_equivalent (M : Machine) :
    ∃ n'' : ℕ, ∀ n : ℕ, n'' < n → ∀ N ∈ survivors n M, fn N = fn M := by sorry

end ObfImpossibility.RiceSimulator
