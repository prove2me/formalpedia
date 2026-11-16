-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_Supplement_theorem_1_2
-- name    : MinCostArbPacking.Main.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:48:02.289215+00:00
-- url     : https://prove2.me/theorems/b45611cf-67f6-4823-9e5b-f67f04728b3b
-- title:
--   Theorem 1.2 — deterministic minimum-cost maximum-cardinality undirected forest packing
-- statement:
--   Let G be an undirected multigraph with n≥2 vertices and m edges, let k≥1 be any integer, and let c(e) be arbitrary real edge costs, of either sign. There is a deterministic program returning a maximum-cardinality union I of k edge-disjoint forests and its forest decomposition; among every such maximum-cardinality subset J of the original edges, c(I)≤c(J).
--
--   Fix a correct deterministic integral minimum-cost maximum-flow program with monotone worst-case runtime MCF(N,M) for polynomially bounded integer costs and capacities. There are a uniform integer dilation a≥1 and a positive constant C, independent of G,k and c, such that the forest program runs within
--
--   $$C\left[kL(kn)\,\operatorname{MCF}(am,am)+k^3nL(n)L(kn)^3+k^5nL(kn)^3\right],\qquad L(x)=\max\{1,\log_2x\}.$$
--
--   When m=0, the flow term is omitted and the empty forest is returned without a flow call. Network construction, flow execution, input handling and output labels are charged in the published machine model; its word exponent is fixed before all inputs. No regularity under dilation is required of MCF. This companion theorem uses Lemma 6.2 and Theorem 6.1; it is not used in the proof of the mission goal.
--
--   Differences from the source:
--   - encoding: a finite directed or undirected multigraph → the published edge-identity multigraph with vertices Fin n and edges Fin m; reason: finite relabelling preserves loops, parallel edges, isolated vertices and all original competing subsets; in the undirected case endpoint order is ignored by forest independence
--   - encoding: a deterministic algorithm in the exact-arithmetic model of §3.1 with O(f) runtime → a fixed published-machine program, polynomial word exponent and positive time constant chosen before all graph and cost inputs, halting within C times f; reason: instruction iteration supplies the intrinsic step count, and constants cannot depend on graph size, k or real costs
--   - encoding: a forest decomposition of the selected set → one output label per original edge, 0 for unselected and i+1 for forest i, decoded with the published predicates; reason: this represents exactly a disjoint k-forest decomposition; actual input and output work is charged by the interpreter
--   - encoding: MCF(N,M) is the runtime of a correct deterministic integral minimum-cost maximum-flow algorithm for polynomial integer data → for every fixed actual program Q, fixed polynomial magnitude degree d≥1 and monotone runtime envelope satisfying MCFContract, the forest program exists with the displayed bound; reason: this expands the source runtime parameter into a charged subprogram contract in the same interpreter; the reduction needs costs and capacities at most m, and does not assume an optimization oracle
--   - encoding: MCF(O(m),O(m)) in (1.2) → MCF(a*m,a*m), with one integer a≥1 chosen before every graph input, and no flow term when m=0; reason: the uniform dilation exposes both hidden network-size constants without assuming regularity of MCF under dilation; omitting isolated vertices gives O(m) nodes, while the n terms cover their bookkeeping
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), Theorem 1.2, p. 2

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Supplement_Weighted
import Definitions.Def_MinCostArbPacking_Main_Supplement_IntegralFlow
set_option autoImplicit false

namespace MinCostArbPacking.Main.Supplement

/-- Theorem 1.2, p.2 (restated p.28): deterministic minimum-cost maximum-cardinality
undirected k-forest packing, with its decomposition and the complete MCF-parameterized bound.
The flow subprogram is an actual program of the published machine, with a charged runtime
contract. The output program uses the same instruction set. Dilation a and time constant C
are chosen uniformly before every input; no regularity under dilation is imposed on MCF. -/
theorem theorem_1_2 (Q : Machine.Program) (flowCW d : ℕ) (MCF : ℕ → ℕ → ℝ)
    (hMCF : MCFContract Q flowCW d MCF) :
    ∃ (P : Machine.Program) (cw a : ℕ) (C : ℝ), 1 ≤ a ∧ 0 < C ∧
      ∀ X : WeightedInput, 2 ≤ X.n → 1 ≤ X.k → ∀ W : ℤ,
        ((X.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
          Machine.HaltsWithin P W X.inI X.inR (C * undirectedBound MCF a X.toDigraphInput)
            (fun o _ => WeightedOutput X o) := by sorry

end MinCostArbPacking.Main.Supplement
