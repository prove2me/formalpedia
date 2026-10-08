-- Prove2me | Theorems.Thm_ObfImpossibility_RiceSimulator_theorem_A_2
-- name    : ObfImpossibility.RiceSimulator.theorem_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:34.330475+00:00
-- url     : https://prove2.me/theorems/b7cf1ad7-7002-47d9-8364-1a2d30ea2afa
-- title:
--   Theorem A.2 (Rice's Theorem, second generalization) — a decidable promise problem closed under $[\cdot]$ is decided by a simulator with $\langle M\rangle$ and $1^{|M|}$
-- statement:
--   Let $\Pi=(\Pi_Y,\Pi_N)$ be a promise problem on machines that is closed under $[\cdot]$ (functionally equivalent machines lie in the same parts of $\Pi$) and decidable (some machine $T$ outputs $1$ on the description of every $M\in\Pi_Y$ and $0$ on the description of every $M\in\Pi_N$). Then there exists a single oracle machine $S$ such that, for every machine $M$,
--   $$M\in\Pi_Y\ \Rightarrow\ S^{\langle M\rangle}(1^{|M|})=1,\qquad M\in\Pi_N\ \Rightarrow\ S^{\langle M\rangle}(1^{|M|})=0 .$$
--   Here $S$ receives only the size $|M|$ of $M$ as input and oracle access to the bounded-run function $\langle M\rangle(1^t,x)$; it does not see the description of $M$. Both equalities include that $S$ halts.
--
--   This is the paper's computability-theoretic form of the slogan "the only useful thing you can do with a machine is run it": any semantic property of machines that can be decided from their code, even only on a promise, can already be decided by running the machine on inputs of one's choice for budgets of one's choice, given a bound on its size.
--
--   **Formalization Note** $S$ is a uniform oracle program (`FriedbergMuchnik.Program`) chosen before $M$; $S^{\langle M\rangle}(z)$ is `oracleEval` with the total oracle `oracle M`. The input $1^{|M|}$ is passed as the number $|M|$ = `Nat.size (encode M)` (unary versus binary is immaterial for computability); it is not the description of $M$, and many machines share each size. $\langle M\rangle(1^t,x)$ is Mathlib's fuel-bounded evaluation `Code.evaln t M x`.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:41, Theorem A.2

import Mathlib
import Definitions.Def_ObfImpossibility_RiceSimulator_Setting

namespace ObfImpossibility.RiceSimulator

/-- Theorem A.2 (Rice's Theorem — second generalization), p. A:41: if a promise problem
`Π` closed under `[·]` is decidable, then one oracle machine `S` decides it from oracle
access to `⟨M⟩` and the input `|M|`. -/
theorem theorem_A_2 (P : PromiseProblem) (hclosed : P.ClosedUnderFn) (hdec : P.IsDecidable) :
    ∃ S : FriedbergMuchnik.Program,
      (∀ M ∈ P.yes, simRun S M (size M) = Part.some 1) ∧
      (∀ M ∈ P.no, simRun S M (size M) = Part.some 0) := by sorry

end ObfImpossibility.RiceSimulator
