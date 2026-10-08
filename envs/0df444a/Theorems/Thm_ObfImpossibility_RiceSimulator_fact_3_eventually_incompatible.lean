-- Prove2me | Theorems.Thm_ObfImpossibility_RiceSimulator_fact_3_eventually_incompatible
-- name    : ObfImpossibility.RiceSimulator.fact_3_eventually_incompatible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:20.337025+00:00
-- url     : https://prove2.me/theorems/8b254359-62e6-4f9f-bbea-cae9f8b32a54
-- title:
--   Fact (3), p. A:41 — if $[M]\not\equiv[N]$ then $N$ is eventually not $n$-compatible with $M$
-- statement:
--   Let $M$ and $N$ be machines whose computed partial functions differ, $[M]\not\equiv[N]$. Then there is a number $n'$ such that
--   $$\forall n>n':\quad N \text{ is not } n\text{-compatible with } M.$$
--
--   Functional inequivalence is witnessed by a finite amount of bounded computation, and compatibility at stage $n$ inspects all budgets and inputs up to $n$; this fact is what eventually removes every inequivalent machine from the simulator's candidate sets $S_n$ in the proof of Theorem A.2.
--
--   **Formalization Note** $[M]\not\equiv[N]$ is inequality of the partial functions `Code.eval M` and `Code.eval N`: they may differ in a value or in where they are defined.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:41, proof of Theorem A.2, fact (3)

import Mathlib
import Definitions.Def_ObfImpossibility_RiceSimulator_Setting

namespace ObfImpossibility.RiceSimulator

/-- Fact (3), p. A:41: if `[M] ≢ [N]` then there is `n'` such that `N` is not
`n`-compatible with `M` for all `n > n'`. -/
theorem fact_3_eventually_incompatible (M N : Machine) (h : fn M ≠ fn N) :
    ∃ n' : ℕ, ∀ n : ℕ, n' < n → ¬ Compatible n N M := by sorry

end ObfImpossibility.RiceSimulator
