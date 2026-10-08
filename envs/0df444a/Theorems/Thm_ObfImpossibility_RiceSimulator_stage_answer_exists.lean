-- Prove2me | Theorems.Thm_ObfImpossibility_RiceSimulator_stage_answer_exists
-- name    : ObfImpossibility.RiceSimulator.stage_answer_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:05.125243+00:00
-- url     : https://prove2.me/theorems/44c653fe-33c2-4ee1-bd67-c1b4ebeddec3
-- title:
--   pp. A:41–A:42 — the simulator halts on every instance of the promise
-- statement:
--   Let $\Pi=(\Pi_Y,\Pi_N)$ be a promise problem closed under $[\cdot]$ and let $T$ be a machine that decides $\Pi$. Then:
--
--   1. for every $M\in\Pi_Y$ there is a stage $n$ at which $T$, run for $n$ steps, halts on every machine of $S_n$ with output $1$;
--   2. for every $M\in\Pi_N$ there is a stage $n$ at which $T$, run for $n$ steps, halts on every machine of $S_n$ with output $0$.
--
--   Here $S_n$ is the set of machines of size $|M|$ that are $n$-compatible with $M$. In other words, the simulator of Theorem A.2 halts on every promise instance, with the answer $T(\ulcorner M\urcorner)$. This is the termination half of the proof of Theorem A.2.
--
--   **Formalization Note** The paper says "S always halts"; its argument (and the statement here) covers only $M\in\Pi_Y\cup\Pi_N$, where $T$ is guaranteed to halt. Outside the promise $T$, and hence the simulator, may diverge.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, pp. A:41–A:42, proof of Theorem A.2

import Mathlib
import Definitions.Def_ObfImpossibility_RiceSimulator_Setting

namespace ObfImpossibility.RiceSimulator

/-- pp. A:41–A:42: the simulator halts on every instance of the promise: for `M ∈ Π_Y`
(resp. `Π_N`) some stage `n` stops with answer `1` (resp. `0`), the answer of `T(M)`. -/
theorem stage_answer_exists (P : PromiseProblem) (hclosed : P.ClosedUnderFn)
    (T : Machine) (hT : Decides T P) :
    (∀ M ∈ P.yes, ∃ n : ℕ, StageAnswer T M n 1) ∧
    (∀ M ∈ P.no, ∃ n : ℕ, StageAnswer T M n 0) := by sorry

end ObfImpossibility.RiceSimulator
