-- Prove2me | Theorems.Thm_NisanRonen_Rounding_rounded_problem_exact_polytime
-- name    : NisanRonen.Rounding.rounded_problem_exact_polytime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:24:10.216994+00:00
-- url     : https://prove2.me/theorems/2f9abde2-fce7-4de4-b400-cdc6b4c2d686
-- title:
--   The rounded bounded scheduling problem is solved exactly in polynomial time
-- statement:
--   Fix the number of agents $n \ge 1$, bounds $0 < a < b$ and a grid step $\delta > 0$. There is an allocation algorithm $f$ on rounded instances such that
--
--   1. $f$ is computable by a Turing machine in time polynomial in the length of the binary encoding of its input, and
--   2. $f$ is an exact solver of the rounded problem: on every matrix of declared times $d \in [a,b]^{n \times k}$, for any number $k$ of tasks, it returns one agent per task and its allocation $x$ satisfies
--   $$
--   \hat g\big(x, \mathrm{corr}^*(x, d)\big) = \min_y \hat g\big(y, \mathrm{corr}^*(y, d)\big).
--   $$
--
--   This is the algorithmic half of the rounding mechanism: the allocation it uses is an exact optimum of the rounded problem and can be computed efficiently when the number of agents is fixed.
--
--   Differences from the source:
--   - encoding: agents 1, …, n and tasks 1, …, k → `Fin n` and `Fin k`, i.e. 0, …, n − 1 and 0, …, k − 1; reason: Lean indexing convention; the same instances
--   - encoding: n agents → `[NeZero n]`, i.e. n ≥ 1; reason: with no agents and at least one task there is no allocation and no make-span; the paper's n agents are at least one
--   - reading: "It then exactly solves this rounded problem using dynamic programming" (the algorithm of Horowitz and Sahni) → there exists an algorithm computable in polynomial time that is an exact solver of the rounded problem on every instance with entries in [a, b]; reason: the paper specifies the algorithm only as an exact polynomial-time solver of the rounded bounded problem; exactness is required on the bounded instances, which are the rounded problem's instances (Def. 33)
--   - reading: "in polynomial time" (no computation model fixed) → Mathlib's `Turing.TM2ComputableInPolyTime` on the binary encoding `encodeInstance` of the δ-unit instance, polynomial in the input length on every input; reason: the standard Turing-machine notion with binary numbers; a real declaration has no finite encoding, so the machine reads the rounded instance in δ-units
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, p. 192 (PDF p. 27), unnumbered: "It then exactly solves this rounded problem using dynamic programming (in polynomial time)."

import Mathlib
import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver
import Definitions.Def_NisanRonen_Rounding_encodeInstance

namespace NisanRonen.Rounding

/-- **The rounded problem is solved exactly in polynomial time** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), p. 192,
unnumbered: "It then exactly solves this rounded problem using dynamic programming (in polynomial
time)"). For a fixed number `n ≥ 1` of agents, fixed `b > a > 0` and a fixed grid `δ > 0`, there
is an allocation algorithm on δ-unit instances that is computable in polynomial time by a
Turing machine (Mathlib's `TM2ComputableInPolyTime`, binary input encoding `encodeInstance`,
output a list of agents) and is an exact solver of the rounded problem on every instance with
entries in `[a, b]`.

**Formalization Note** "Polynomial time" is read as Mathlib's `Turing.TM2ComputableInPolyTime`
(the paper fixes no model); the polynomial is uniform in the number `k` of tasks and may depend
on the fixed `n`, `a`, `b`, `δ`. The machine must run in polynomial time on every input, not
only on in-box instances. -/
theorem rounded_problem_exact_polytime {a b δ : ℝ} (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (n : ℕ) [NeZero n] :
    ∃ f : List (Fin n → ℕ) → List (Fin n),
      Nonempty (Turing.TM2ComputableInPolyTime (encodeInstance (n := n))
        (id : List (Fin n) → List (Fin n)) f) ∧
      IsExactRoundedSolver f δ a b := by sorry

end NisanRonen.Rounding
