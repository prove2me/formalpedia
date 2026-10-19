-- Prove2me | Theorems.Thm_OAI_ErdosGallai_lovasz_path_cycle_decomposition
-- name    : OAI.ErdosGallai.lovasz_path_cycle_decomposition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:04:10.880935+00:00
-- url     : https://prove2.me/theorems/85362689-c5fd-4c43-83a4-7464add8171f
-- title:
--   Lovász's theorem: every graph on n vertices decomposes into at most ⌊n/2⌋ paths and cycles
-- statement:
--   Let $G$ be a simple graph on a finite vertex type $V$ (`[Fintype V]`). Then there are a number $k$ with $2k \le |V|$ and edge sets $E_0, \dots, E_{k-1} \subseteq \mathrm{Sym2}\ V$ (`parts : Fin k → Set (Sym2 V)`) with the following properties.
--   - Each $E_i$ is either the edge set of a path of positive length in $G$ (`p.IsPath ∧ 0 < p.length`), or the edge set of a cycle in $G$ (`p.IsCycle`).
--   - The $E_i$ are pairwise disjoint.
--   - Their union is the edge set of $G$.
--
--   In words: the edges of every graph on $n$ vertices can be partitioned into at most $\lfloor n/2 \rfloor$ paths and cycles (Lovász 1968).
--
--   Lean: `OAI.ErdosGallai.lovasz_path_cycle_decomposition`. This is OpenAI's theorem `lovasz_path_cycle_partition` in `lean/OAI/Combinatorics/CycleDecomposition/EndpointPartition.lean`, with OpenAI's definitions `LovaszPathCyclePartition` and `PathOrCycleEdgeSet` written out, so that the statement uses only Mathlib.
-- source:
--   L. Lovász, On covering of graphs, in Theory of Graphs (Proc. Colloq., Tihany, 1966), Academic Press, New York, 1968, 231–236. Lean proof: OpenAI, A linear cycle-and-edge decomposition of every graph, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 181; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CycleDecomposition/EndpointPartition.lean (declaration OAI.ErdosGallai.lovasz_path_cycle_partition, stated here with its two definitions written out)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section

namespace ErdosGallai
noncomputable section

theorem lovasz_path_cycle_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V)),
      (∀ i, (∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ 0 < p.length ∧ parts i = p.edgeSet) ∨
        (∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ parts i = p.edgeSet)) ∧
      Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
      (⋃ i, parts i) = G.edgeSet ∧ 2 * k ≤ Fintype.card V := by
  sorry

end
end ErdosGallai

end
end
end

end OAI
end
