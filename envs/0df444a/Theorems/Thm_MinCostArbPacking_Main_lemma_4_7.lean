-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_7
-- name    : MinCostArbPacking.Main.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:25.898295+00:00
-- url     : https://prove2.me/theorems/339c4bd1-a85d-46b6-b8e9-acff1fffb245
-- title:
--   Lemma 4.7 — a compatible batch is optimal
-- statement:
--   **Lemma 4.7 (A compatible batch is optimal).** Assume the standing assumptions of §4.2, with $b=\deg^{in}_I$ and proposals $P_T$ from deficient vertices $u_T$ of the deficient blocks. Let $A'$ be any compatible set of terminals, $U=\{u_T:e_T\in A'\}$, and
--
--   $$I'=I\oplus\bigcup_{T:e_T\in A'}P_T .$$
--
--   Then $I'$ is a minimum-cost independent set with indegree vector $b+\mathbf 1_U$.
--
--   This is the optimality half of the batching framework.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §3.1 and §4.2 (loops and arcs entering $r$ deleted; $I$ independent, cheapest for its indegree vector, no arc into $r$, indegree $\le k$) → explicit hypotheses `NoLoopNoRootArc` and `Standing`; reason: the source states them once for the whole section; they are hypotheses of every lemma there
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.2.3, p.13, Lemma 4.7

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.7 (A compatible batch is optimal), p.13: for any compatible set `A'` of terminals, with
`U = {u_T : e_T ∈ A'}` and `I' = I ⊕ ⋃_{T : e_T ∈ A'} P_T`, the set `I'` is a minimum-cost
independent set with indegree vector `b + 1_U`, where `b = deg^in_I`. -/
theorem lemma_4_7 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (r : V) (c : E → ℝ)
    (hG : G.NoLoopNoRootArc r) (I : Finset E) (hI : G.Standing k r c I)
    (u : Finset V → V) (P : Finset V → List E) (hP : G.IsProposalSystem k r c I u P)
    (A' : Finset E) (hA : G.Compatible k r I P A') :
    G.IndepK k (G.execute k r I P A') ∧
    (∀ v, G.inDeg (G.execute k r I P A') v =
      addOne (fun w => G.inDeg I w) (G.chosenVertices k r I u P A') v) ∧
    ∀ X, G.IndepK k X →
      (∀ v, G.inDeg X v = addOne (fun w => G.inDeg I w) (G.chosenVertices k r I u P A') v) →
      cost c (G.execute k r I P A') ≤ cost c X := by sorry

end MinCostArbPacking.Main
