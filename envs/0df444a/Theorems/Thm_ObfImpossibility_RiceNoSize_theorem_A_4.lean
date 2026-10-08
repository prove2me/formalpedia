-- Prove2me | Theorems.Thm_ObfImpossibility_RiceNoSize_theorem_A_4
-- name    : ObfImpossibility.RiceNoSize.theorem_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:40.624688+00:00
-- url     : https://prove2.me/theorems/f5d5754f-d2d3-4263-81b7-576193b2a176
-- title:
--   Theorem A.4 — Conjecture A.3 is false: without $1^{|M|}$ a simulator with oracle $\langle M\rangle$ cannot decide every decidable $\Pi$ closed under $[\cdot]$
-- statement:
--   **Theorem A.4.** Conjecture A.3 is false. That is, there is a promise problem $\Pi=(\Pi_Y,\Pi_N)$ — a pair of disjoint sets of Turing machines — that is closed under $[\cdot]$ and decidable, such that no oracle machine $S$ satisfies
--   $$M\in\Pi_Y\Rightarrow S^{\langle M\rangle}()=1,\qquad M\in\Pi_N\Rightarrow S^{\langle M\rangle}()=0,$$
--   where $S^{\langle M\rangle}()$ is the output of $S$ given oracle access to the step-bounded function $\langle M\rangle(1^t,x)$ and nothing else.
--
--   Theorem A.2 shows that such an $S$ exists when it is also given $1^{|M|}$; Theorem A.4 shows that this extra input cannot be dropped, so the computability analogue of the virtual-black-box simulator needs an upper bound on the size of the program.
--
--   **Formalization Note** Machines are step-counted one-tape Turing machines with unary inputs, $|M|$ is the number of states, and oracle machines are uniform oracle programs run on the fixed input $0$ (see the setting file).
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:42, Theorem A.4

import Mathlib
import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects

namespace ObfImpossibility.RiceNoSize

/-- Theorem A.4 (p. A:42): Conjecture A.3 is false. -/
theorem theorem_A_4 : ¬ ConjectureA3 := by sorry

end ObfImpossibility.RiceNoSize
