-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_Supplement_theorem_6_1
-- name    : MinCostArbPacking.Main.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:48:35.419274+00:00
-- url     : https://prove2.me/theorems/58c75fef-7e78-403f-98cf-d0fb57d7c8bf
-- title:
--   Theorem 6.1 — deterministic weighted forest packing with vertex-specific indegree bounds
-- statement:
--   Let G be a finite directed multigraph on n vertices with m arcs, k≥1 any integer, real arc costs c(e) of either sign, and bounds b(v)∈{0,…,k} specified separately at every vertex. A subset J is feasible when it is a union of k forests of the underlying undirected multigraph and its selected-set indegree at every v is at most b(v). No root is specified and the input graph's own indegrees are unrestricted.
--
--   One deterministic program returns a feasible set I, a disjoint decomposition into k forests, and the guarantees
--
--   $$\forall\text{ feasible }J,\quad |J|\le|I|,\qquad |J|=|I|\Longrightarrow\sum_{e\in I}c(e)\le\sum_{e\in J}c(e).$$
--
--   For a uniform positive constant C its executed instructions are at most C times
--
--   $$F(n,m,k)=kmL(kn)+k^2nL(n)L(kn)^2+k^4nL(kn)^2,\qquad L(x)=\max\{1,\log_2x\}.$$
--
--   The program and its polynomial word exponent and C are fixed before every input, independently of costs and k. One-vertex inputs are included, including arbitrary loops; their selected forests are empty. At n=0 the bound uses max{1,F} to cover constant empty-instance overhead; for n≥1 it equals F. This companion theorem follows from the published Theorem 1.1 and also supports Theorem 1.2; it is not a prerequisite of the mission goal.
--
--   Differences from the source:
--   - encoding: a finite directed or undirected multigraph → the published edge-identity multigraph with vertices Fin n and edges Fin m; reason: finite relabelling preserves loops, parallel edges, isolated vertices and all original competing subsets; in the undirected case endpoint order is ignored by forest independence
--   - encoding: a deterministic algorithm in the exact-arithmetic model of §3.1 with O(f) runtime → a fixed published-machine program, polynomial word exponent and positive time constant chosen before all graph and cost inputs, halting within C times f; reason: instruction iteration supplies the intrinsic step count, and constants cannot depend on graph size, k or real costs
--   - encoding: a forest decomposition of the selected set → one output label per original edge, 0 for unselected and i+1 for forest i, decoded with the published predicates; reason: this represents exactly a disjoint k-forest decomposition; actual input and output work is charged by the interpreter
--   - encoding: the asymptotic runtime in Theorem 6.1 for finite graphs → C*max{1,F(n,m,k)} on all inputs, including n=0; reason: for n≥1 and k≥1 the exact three-term expression F is at least one and unchanged; n=0 forces m=0 and needs only constant empty-instance overhead
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), Theorem 6.1, p. 26-27

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Supplement_Weighted
set_option autoImplicit false

namespace MinCostArbPacking.Main.Supplement

/-- Theorem 6.1, pp.26–27: rootless weighted forest packing with arbitrary vertexwise bounds.
The max with 1 covers constant empty-instance overhead only; for n≥1,k≥1 the bound is unchanged.
One fixed program, word exponent and positive time constant precede every graph and cost input. -/
theorem theorem_6_1 : ∃ (P : Machine.Program) (cw : ℕ) (C : ℝ), 0 < C ∧
    ∀ X : BoundedInput, 1 ≤ X.k → (∀ v, X.b v ≤ X.k) → ∀ W : ℤ,
      ((X.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
        Machine.HaltsWithin P W X.inI X.inR (C * max 1 (forestBound X.toDigraphInput))
          (fun o _ => BoundedOutput X o) := by sorry

end MinCostArbPacking.Main.Supplement
