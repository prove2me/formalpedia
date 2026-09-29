-- Prove2me | Theorems.Thm_OPG500Counterexample_core_link_rank_gap
-- name    : OPG500Counterexample.core_link_rank_gap
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-07T04:08:07.84527+00:00
-- url     : https://prove2.me/theorems/da116936-f943-4b93-b275-8792b58d28eb
-- title:
--   The four-core link-pattern rank gap
-- statement:
--   Let $F$ be a triangle-free simple graph on $\{0,1,2,3\}$. For each $i$, let $N_i$ be a vertex set not containing $i$. Assume that whenever $j\neq i$ and $j\notin N_i$, the vertex $j$ has a neighbor in $N_i$. Then
--
--   $$
--   7<|E(F)|+\sum_{i=0}^{3}\#\pi_0(F[N_i]),
--   $$
--
--   where $F[N_i]$ is the subgraph induced by $N_i$ and $\#\pi_0$ counts its connected components. This is a finite four-vertex combinatorial statement.
-- source:
--   Candidate C10, Sections T4 and T5: https://github.com/vibemathing/problem-opg-500-geodesic-cycles/blob/a41fe59b4535851ea55f6e868e938b9aaf81e924/research/artifacts/candidates/opg500-a01-c10/tight-rank.md

import Definitions.Def_opg500_weighted_cycle_models

namespace OPG500Counterexample

/-- The finite four-core combinatorial obstruction used by the all-ties route.
Every triangle-free core with four link sets avoiding their indexed vertices and
dominating all omitted vertices has a strictly positive cycle-rank gap. -/
theorem core_link_rank_gap
    (F : SimpleGraph (Fin 4)) [DecidableRel F.Adj]
    (N : Fin 4 → Finset (Fin 4))
    (htriangleFree : ∀ ⦃a b c : Fin 4⦄,
      a ≠ b → b ≠ c → a ≠ c →
        ¬ (F.Adj a b ∧ F.Adj b c ∧ F.Adj c a))
    (havoids : ∀ i v, v ∈ N i → v ≠ i)
    (hdominates : ∀ i j, j ≠ i → j ∉ N i →
      ∃ k, k ∈ N i ∧ F.Adj j k) :
    7 < F.edgeFinset.card +
      ∑ i, Nat.card (F.induce {v | v ∈ N i}).ConnectedComponent := by sorry

end OPG500Counterexample
