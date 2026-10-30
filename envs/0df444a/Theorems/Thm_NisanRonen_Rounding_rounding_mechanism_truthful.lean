-- Prove2me | Theorems.Thm_NisanRonen_Rounding_rounding_mechanism_truthful
-- name    : NisanRonen.Rounding.rounding_mechanism_truthful
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:28:07.953803+00:00
-- url     : https://prove2.me/theorems/024d9e2a-a7b4-405d-b202-c7f4d557a424
-- title:
--   Truth-telling is a dominant strategy of the rounding mechanism
-- statement:
--   Let $0 < a < b$, $\delta > 0$, and let the allocation algorithm $f$ be any exact solver of the rounded problem. For every type matrix $t$ of $n \ge 1$ agents and $k$ tasks with $a \le t^i_j \le b$, and every agent $i$, the truthful strategy (declare $t^i$, execute every allocated task in time $t^i_j$) is a dominant strategy of agent $i$ under the rounding mechanism.
--
--   When the types and the actual times are rounded, $\hat g$ is the make-span of the rounded instance and the allocation algorithm is optimal for it; the bonus therefore aligns each agent with the rounded optimum. No tie-breaking rule is needed for this clause.
--
--   Differences from the source:
--   - encoding: agents 1, …, n and tasks 1, …, k → `Fin n` and `Fin k`, i.e. 0, …, n − 1 and 0, …, k − 1; reason: Lean indexing convention; the same instances
--   - encoding: n agents → `[NeZero n]`, i.e. n ≥ 1; reason: with no agents and at least one task there is no allocation and no make-span; the paper's n agents are at least one
--   - reading: declarations d^i chosen "in an unrestricted manner" (Def. 18), while the agents' declarations "are simply to report their types" (Def. 19) and types lie in [a, b]^k (Def. 33) → every declaration (the agent's own and the others') ranges over [a, b]^k; reason: the rounding algorithm is defined only on bounded instances (Def. 33); on unbounded rounded instances exact scheduling on unrelated machines is NP-hard, so no polynomial exact solver exists there
--   - encoding: dominance against all strategies of the other agents (Def. 3) → dominance quantifies over all profiles of the others with in-box declarations and unconstrained executions; reason: agent i's utility depends on the others only through their declarations (Def. 22 uses declared times for their tasks; proof of Claim 5.2, p. 188), so constraining their executions changes nothing
--   - encoding: the bonus uses the allocation x(t̂) and the compensation x(t) (Def. 34) → one allocation `allocOf f δ d`, computed from the δ-unit instance `units δ d`; reason: the algorithm reads only the rounded instance, and ⌈roundUp δ v / δ⌉ = ⌈v / δ⌉, so x(t̂) = x(t)
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, proof (sketch) of Theorem 5.9, p. 193 (PDF p. 28): "When the types and the actual computation times are rounded, ĝ is exactly the make-span, and the rounding algorithm is optimal." … "In particular, truth-telling is among the dominant strategies."

import Mathlib
import Definitions.Def_NisanRonen_Rounding_IsDominant
import Definitions.Def_NisanRonen_Rounding_truthStrategy
import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver

namespace NisanRonen.Rounding

/-- **Truth-telling is a dominant strategy of the rounding mechanism** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), proof
(sketch) of Theorem 5.9, p. 193: "When the types and the actual computation times are rounded, ĝ
is exactly the make-span, and the rounding algorithm is optimal." … "In particular, truth-telling
is among the dominant strategies"). In the bounded problem (`0 < a < b`, types in `[a, b]`) with
grid `δ > 0`, if the allocation algorithm `f` is any exact solver of the rounded problem, then for
every type matrix `t` with entries in `[a, b]` and every agent `i`, declaring `t^i` and executing
every allocated task in time `t^i_j` is a dominant strategy of agent `i`.

**Formalization Note** No tie-breaking rule is needed: this holds for every exact rounded
solver. -/
theorem rounding_mechanism_truthful {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t : Fin n → Fin k → ℝ) (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b) :
    ∀ i : Fin n, IsDominant f δ a b i (t i) (truthStrategy (t i)) := by sorry

end NisanRonen.Rounding
