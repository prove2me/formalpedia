-- Prove2me | Theorems.Thm_FriedbergMuchnik_priority_permanent_follower_safety
-- name    : FriedbergMuchnik.priority_permanent_follower_safety
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T21:55:18.980246+00:00
-- url     : https://prove2.me/theorems/5689a395-2b10-48bb-88b1-348e390fdf71
-- title:
--   Enumeration and computation preservation for a permanent follower
-- statement:
--   Consider the fixed priority construction. Let $q,a,x\in\mathbb N$ and let $b$ be a Boolean flag. Assume that $q<a$ and that the entry for requirement $q$ at every stage $s\ge a$ is exactly the same pair $(x,b)$. Put $i=\operatorname{side}(q)$, let $c_q$ be the program with index $\lfloor q/2\rfloor$, and write $A_i=\bigcup_s L_{i,s}$ for the limit sets. Then
--
--   $$
--   x\in A_{1-i}\quad\Longleftrightarrow\quad b=\mathrm{true}.
--   $$
--
--   Moreover, if the permanent flag is true, there is a stage $t<a$ with
--
--   $$
--   E_t^{\chi_{L_{i,t}}}(c_q,x)=\operatorname{some}(0)
--   \quad\text{and}\quad
--   L_{i,t}\cap[0,t)=A_i\cap[0,t).
--   $$
--
--   Here $E_t$ is the bounded oracle interpreter and $\chi_{L_{i,t}}$ is the characteristic function of the finite stage list. The result classifies a specified permanent follower and supplies a preserved finite computation for an acted flag. It does not assert existence of a permanent follower or correctness of unbounded oracle evaluation.
-- source:
--   Arnold W. Miller, Lecture notes in Recursion Theory, December 3, 2008, Section 26, Theorem 26.2, pp. 51–54, https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf. Verification cases (a) and (b) on pp. 53–54: distinct, unrepeated follower values and protection of the acted computation by appointing lower priority followers above its use. This conditional interface concerns the actual priorityStage entries and stageList unions. The activation hypothesis and stability of both follower and flag are explicit; prefix preservation uses the interpreter's bound on oracle queries. The combinatorial invariants are now proved directly in Lean: pairing-based follower freshness, monotone appointment stages, exact acted-flag membership, and preservation of the historical oracle prefix.

import Definitions.Def_FriedbergMuchnik_Priority

namespace FriedbergMuchnik

theorem priority_permanent_follower_safety (q a x : ℕ) (b : Bool)
    (hqa : q < a)
    (hstable : ∀ s : ℕ, a ≤ s →
      (priorityStage s).2[q]?.getD (0, false) = (x, b)) :
    (x ∈ limitSet (!(side q)) ↔ b = true) ∧
    (b = true → ∃ t : ℕ, t < a ∧
      oracleEvaln (stateOracle (priorityStage t) (side q)) t
        (Denumerable.ofNat Program (q / 2)) x = some 0 ∧
      ∀ n : ℕ, n < t →
        (n ∈ stageList (side q) t ↔ n ∈ limitSet (side q))) := by sorry

end FriedbergMuchnik
