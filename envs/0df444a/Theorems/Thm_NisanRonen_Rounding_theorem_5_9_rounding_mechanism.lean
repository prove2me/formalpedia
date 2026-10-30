-- Prove2me | Theorems.Thm_NisanRonen_Rounding_theorem_5_9_rounding_mechanism
-- name    : NisanRonen.Rounding.theorem_5_9_rounding_mechanism
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:30:09.782798+00:00
-- url     : https://prove2.me/theorems/ab14b34b-df5a-4f87-b508-f4c84367315c
-- title:
--   Theorem 5.9: the rounding mechanism is a polynomial-time truthful $(1+\epsilon)$-implementation (corrected: some exact solver of the rounded problem)
-- statement:
--   For every fixed $\epsilon > 0$ the rounding mechanism is a polynomial time mechanism with verification that truthfully implements a $1+\epsilon$ approximation for the bounded task scheduling problem. Precisely: for every $\epsilon > 0$ and $a > 0$ there is a grid step $\delta > 0$, depending only on $a$ and $\epsilon$, such that for every $b > a$ and every number $n \ge 1$ of agents there is an allocation algorithm $f$ on rounded instances with the following properties.
--
--   1. **Polynomial-time allocation.** $f$ is computable by a Turing machine in time polynomial in the length of the binary encoding of the rounded instance.
--   2. **Polynomial-time bonus.** The rounded make-span of an allocation on a rounded instance, in $\delta$-units, is computable by a Turing machine in polynomial time.
--   3. **Rounding algorithm.** $f$ is an exact solver of the rounded problem on every instance with entries in $[a,b]$.
--   4. **Truthfulness.** For every type matrix $t$ with $a \le t^i_j \le b$, declaring one's type and executing every allocated task in minimal time is a dominant strategy of every agent.
--   5. **Implementation of a $1+\epsilon$ approximation.** For every type matrix $t$ with entries in $[a,b]$ and every profile $s$ in which every agent plays a dominant strategy, the allocation $x$ and actual times $\tilde t$ produced satisfy
--   $$
--   g(x, \tilde t) \le (1+\epsilon)\, g\big(y, \mathrm{corr}^*(y,t)\big) \quad \text{for every allocation } y .
--   $$
--
--   Here the mechanism allocates with $f$ on the rounded declarations and pays agent $i$ the compensation $\sum_{j \in x^i} \tilde t_j$ plus the bonus $-\hat g(x, \mathrm{corr}^i(x, d, \tilde t))$. The theorem shows that, with verification of the execution times, a polynomial-time mechanism can achieve any approximation ratio above $1$ on bounded instances, while without verification no mechanism achieves a ratio below $2$.
--
--   **Formalization Note** Clause 5 compares against $y$ at the true times only: any feasible output $(y, \tilde t')$ has $\tilde t' \ge \mathrm{corr}^*(y, t)$ entrywise, so the minimal-time output is the binding comparison.
--
--   Differences from the source:
--   - correction: the allocation algorithm is "the rounding algorithm of Horowitz and Sahni", an unspecified exact solver of the rounded problem, and the implementation clause is asserted for it → there exists a polynomial-time exact solver f of the rounded problem (some tie-breaking among rounded optima) for which all five clauses hold; reason: for an arbitrary exact solver the implementation clause is false: n = k = 2, a = 3δ, b = 5δ, ϵ = 1/3, types (3δ, 3δ), (3δ, 5δ); a solver with suitable ties makes the declarations (5δ, 5δ) and (4δ, 4δ) with minimal execution dominant and allocates task 1 to agent 1 and task 2 to agent 2, a rounded optimum (make-span 5δ, a tie), whose true make-span 5δ exceeds (4/3)·3δ; checked for every grid size a/δ from 3 to 30 (planning_numerics/verify_counterexample.py)
--   - reading: "δ (a parameter chosen as a function of a and ϵ)" → ∃ δ > 0 placed after ∀ ϵ, ∀ a and before ∀ b, ∀ n; reason: δ depends on a and ϵ only, as printed
--   - reading: "polynomial time" (no computation model is fixed; p. 172: "the output and payment functions are computable in polynomial time") → Mathlib's `Turing.TM2ComputableInPolyTime` for the allocation algorithm on the δ-unit instance (binary encoding `encodeInstance`) and for the bonus in δ-units (`unitMakespan`, input `encodeInstanceAlloc`, output binary `encodeNat`); reason: the standard Turing-machine notion with binary numbers; real numbers have no finite encoding, so rounding a real declaration to δ-units and the k real additions of the compensation are not part of the machine model
--   - reading: declarations d^i chosen "in an unrestricted manner" (Def. 18), while the agents' declarations "are simply to report their types" (Def. 19) and types lie in [a, b]^k (Def. 33) → every declaration (the agent's own and the others') ranges over [a, b]^k; reason: the rounding algorithm is defined only on bounded instances (Def. 33); on unbounded rounded instances exact scheduling on unrelated machines is NP-hard, so no polynomial exact solver exists there
--   - encoding: dominance against all strategies of the other agents (Def. 3) → dominance quantifies over all profiles of the others with in-box declarations and unconstrained executions; reason: agent i's utility depends on the others only through their declarations (Def. 22 uses declared times for their tasks; proof of Claim 5.2, p. 188), so constraining their executions changes nothing
--   - encoding: "for any other output o′ ∈ F, g(o, t) ≤ c · g(o′, t)" (Def. 2) → g(x, t̃) ≤ (1 + ϵ) · g(y, corr*(y, t)) for every allocation y; reason: every feasible output (y, t̃′) has t̃′ ≥ corr*(y, t) entrywise, so the minimal-time outputs are the binding comparison
--   - encoding: the bonus uses the allocation x(t̂) and the compensation x(t) (Def. 34) → one allocation `allocOf f δ d`, computed from the δ-unit instance `units δ d`; reason: the algorithm reads only the rounded instance, and ⌈roundUp δ v / δ⌉ = ⌈v / δ⌉, so x(t̂) = x(t)
--   - encoding: n agents → `[NeZero n]`, i.e. n ≥ 1; reason: with no agents and at least one task there is no allocation and no make-span; the paper's n agents are at least one
--   - encoding: agents 1, …, n and tasks 1, …, k → `Fin n` and `Fin k`, i.e. 0, …, n − 1 and 0, …, k − 1; reason: Lean indexing convention; the same instances
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Theorem 5.9, p. 193 (PDF p. 28); Definition 34 (p. 193), Definition 33 and the rounding algorithm (p. 192), Definitions 2–3 (pp. 171–172), Definitions 18–20 (pp. 186–187)

import Mathlib
import Definitions.Def_NisanRonen_Rounding_IsDominant
import Definitions.Def_NisanRonen_Rounding_truthStrategy
import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver
import Definitions.Def_NisanRonen_Rounding_encodeInstance
import Definitions.Def_NisanRonen_Rounding_encodeInstanceAlloc
import Definitions.Def_NisanRonen_Rounding_unitMakespan

namespace NisanRonen.Rounding

/-- **Theorem 5.9** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), p. 193), corrected: "For every fixed ϵ > 0 the rounding
mechanism is a polynomial time mechanism with verification that truthfully implements a 1 + ϵ
approximation for the bounded task scheduling problem."

For every `ϵ > 0` and `a > 0` there is a grid `δ > 0` (depending on `a` and `ϵ` only) such that for
every `b > a` and every number `n ≥ 1` of agents there is an allocation algorithm `f` on δ-unit
instances with:

1. `f` is computable in polynomial time (Turing machine, binary encoding);
2. the bonus, in δ-units, is computable in polynomial time (`unitMakespan`);
3. `f` is an exact solver of the rounded problem (the rounding algorithm of p. 192);
4. truthfulness (Definition 19): for every type matrix with entries in `[a, b]`, declaring one's
   type and executing in minimal time is a dominant strategy of every agent;
5. implementation (Definition 3, second bullet): for every type matrix with entries in `[a, b]`
   and every profile of dominant strategies, the make-span of the resulting allocation at the
   actual times is at most `1 + ϵ` times the make-span of every allocation at the true types.

**Formalization Note** Correction: the paper's mechanism uses "the rounding algorithm of
Horowitz and Sahni", i.e. an unspecified exact solver of the rounded problem. Read for every
exact solver, clause 5 is false (n = k = 2, a = 3δ, b = 5δ, ϵ = 1/3, types (3δ, 3δ), (3δ, 5δ): a
solver with suitable ties makes the declarations (5δ, 5δ), (4δ, 4δ) dominant and outputs make-span
5δ > (4/3)·3δ, for every grid size a/δ). The statement asserts that **some** exact solver (some
tie-breaking) works. Declarations range over `[a, b]^k`; the rounding of real declarations and the
real compensation sum are outside the cost model. -/
theorem theorem_5_9_rounding_mechanism :
    ∀ ε : ℝ, 0 < ε → ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧
      ∀ b : ℝ, a < b → ∀ (n : ℕ) [NeZero n],
        ∃ f : List (Fin n → ℕ) → List (Fin n),
          Nonempty (Turing.TM2ComputableInPolyTime (encodeInstance (n := n))
            (id : List (Fin n) → List (Fin n)) f) ∧
          Nonempty (Turing.TM2ComputableInPolyTime (encodeInstanceAlloc (n := n))
            Computability.encodeNat (unitMakespan (n := n))) ∧
          IsExactRoundedSolver f δ a b ∧
          (∀ (k : ℕ) (t : Fin n → Fin k → ℝ), (∀ i j, a ≤ t i j ∧ t i j ≤ b) →
            ∀ i : Fin n, IsDominant f δ a b i (t i) (truthStrategy (t i))) ∧
          (∀ (k : ℕ) (t : Fin n → Fin k → ℝ), (∀ i j, a ≤ t i j ∧ t i j ≤ b) →
            ∀ s : Fin n → Strategy n k, (∀ i, IsDominant f δ a b i (t i) (s i)) →
            ∀ y : Fin k → Fin n,
              makespan (allocOf f δ (fun i => (s i).decl)) (actualTimes f δ s) ≤
                (1 + ε) * makespan y (corrStar y t)) := by sorry

end NisanRonen.Rounding
