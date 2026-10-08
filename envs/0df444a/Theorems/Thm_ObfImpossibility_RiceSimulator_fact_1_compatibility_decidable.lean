-- Prove2me | Theorems.Thm_ObfImpossibility_RiceSimulator_fact_1_compatibility_decidable
-- name    : ObfImpossibility.RiceSimulator.fact_1_compatibility_decidable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:05.347998+00:00
-- url     : https://prove2.me/theorems/e81219fe-12ad-4448-a05e-8f42034b6155
-- title:
--   Fact (1), p. A:41 — $n$-compatibility with $M$ is decidable with oracle access to $\langle M\rangle$
-- statement:
--   Let $M$ and $N$ be machines and $n\in\mathbb N$, and recall that $N$ is $n$-compatible with $M$ when $\langle N\rangle(1^t,x)=\langle M\rangle(1^t,x)$ for all $t\le n$ and all inputs $x$ with $|x|\le n$.
--
--   There is a single oracle machine $C$ that decides $n$-compatibility with $M$ using only oracle access to $\langle M\rangle$: for all machines $M$, $N$ and all $n$,
--   $$C^{\langle M\rangle}(n,\ulcorner N\urcorner)=\begin{cases}1 & \text{if } N \text{ is } n\text{-compatible with } M,\\ 0 & \text{otherwise.}\end{cases}$$
--   In particular $C$ halts on every input.
--
--   This is fact (1) in the proof of Theorem A.2: the simulator built there recomputes the set $S_n$ of machines of size $|M|$ that are $n$-compatible with $M$ at every stage, and this is the uniform procedure that does it.
--
--   **Formalization Note** The pair $(n,\ulcorner N\urcorner)$ is passed as `Nat.pair n (encode N)`. The same program $C$ must work for every $M$, $N$, $n$ (the existential quantifier precedes them), so the statement asserts uniform computability relative to the oracle, not a per-instance property.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:41, proof of Theorem A.2, fact (1)

import Mathlib
import Definitions.Def_ObfImpossibility_RiceSimulator_Setting

namespace ObfImpossibility.RiceSimulator

/-- Fact (1), p. A:41: `n`-compatibility with `M` can be decided using oracle access to `⟨M⟩`,
by one oracle machine `C` that works for every `M`, on input the pair `(n, N)`. -/
theorem fact_1_compatibility_decidable :
    ∃ C : FriedbergMuchnik.Program, ∀ (M N : Machine) (n : ℕ),
      (Compatible n N M → simRun C M (Nat.pair n (Encodable.encode N)) = Part.some 1) ∧
      (¬ Compatible n N M → simRun C M (Nat.pair n (Encodable.encode N)) = Part.some 0) := by sorry

end ObfImpossibility.RiceSimulator
