-- Prove2me | Theorems.Thm_OAI_ErdosGallai_Scale_exists_long_path_of_vertex_expansion
-- name    : OAI.ErdosGallai.Scale.exists_long_path_of_vertex_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:04:07.635861+00:00
-- url     : https://prove2.me/theorems/74e75f1d-d3ed-42f5-84e0-82fc7b7c3e28
-- title:
--   Depth-first search finds a path on α n/3 vertices in every α-vertex-expanding graph
-- statement:
--   Let $G$ be a simple graph on a finite vertex type $V$ with decidable equality and decidable adjacency. Let $\alpha \le 1$. Assume $G$ is an $\alpha$-vertex expander in the following sense. Every nonempty set $U$ of vertices with $2|U| \le |V|$ has at least $\alpha|U|$ external neighbours, that is, vertices outside $U$ adjacent to some vertex of $U$. In Lean this is written `(Finset.univ.filter (fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v)).card`.
--
--   Then there is a list $L$ of distinct vertices (`L.Nodup`), consecutive ones adjacent (`L.IsChain G.Adj`), with $|L| \ge \alpha|V|/3$. Such a list is a path in $G$ on at least $\alpha|V|/3$ vertices.
--
--   This is the depth-first-search lemma for expanding graphs. Run depth-first search and stop when the unexplored set is half the size of the explored set. At that moment every external neighbour of the unexplored set lies on the current stack, which is a path.
--
--   Lean: `OAI.ErdosGallai.Scale.exists_long_path_of_vertex_expansion`. This is OpenAI's theorem `exists_long_stack` in `lean/OAI/Combinatorics/CycleDecomposition/DepthFirstSearch.lean`, with OpenAI's definitions `VertexExpansion` and `externalNeighbors` written out, so that the statement uses only Mathlib. The vertex type lives in an arbitrary universe (`Type cycleUniverse2`).
-- source:
--   S. Ben-Eliezer, M. Krivelevich and B. Sudakov, The size Ramsey number of a directed path, J. Combin. Theory Ser. B 102 (2012) (the depth-first-search method for long paths in expanding graphs). Lean proof: OpenAI, A linear cycle-and-edge decomposition of every graph, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 181; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CycleDecomposition/DepthFirstSearch.lean (declaration OAI.ErdosGallai.Scale.exists_long_stack, stated here with its definition written out)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
open Finset SimpleGraph
variable {V : Type cycleUniverse2} [Fintype V] [DecidableEq V]

theorem exists_long_path_of_vertex_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hα : α ≤ 1)
    (hexp : ∀ U : Finset V, U.Nonempty → 2 * U.card ≤ Fintype.card V →
      α * U.card ≤ ((Finset.univ.filter (fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v)).card : ℝ)) :
    ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ α * Fintype.card V / 3 ≤ (L.length : ℝ) := by
  sorry

end ErdosGallai.Scale
end
end
end

end OAI
end
