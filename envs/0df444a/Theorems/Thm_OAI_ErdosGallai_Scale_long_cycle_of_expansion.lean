-- Prove2me | Theorems.Thm_OAI_ErdosGallai_Scale_long_cycle_of_expansion
-- name    : OAI.ErdosGallai.Scale.long_cycle_of_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:04:09.973952+00:00
-- url     : https://prove2.me/theorems/ee8a8e4d-06f3-4d1e-8939-998d1a305262
-- title:
--   Every α-vertex-expanding graph on n vertices has a cycle of length more than α² n/100
-- statement:
--   Let $G$ be a simple graph on a finite vertex type $V$ with decidable equality and decidable adjacency. Let $0 < \alpha \le 1$. Assume $G$ is an $\alpha$-vertex expander: every nonempty set $U$ of vertices with $2|U| \le |V|$ has at least $\alpha|U|$ external neighbours. This is written out exactly as in `exists_long_path_of_vertex_expansion`. Assume also $1 \le \alpha^2|V|/100$ (`hq`).
--
--   Then $G$ has a cycle (`c : G.Walk a a` with `c.IsCycle`) of length greater than $\alpha^2|V|/100$.
--
--   Lean: `OAI.ErdosGallai.Scale.long_cycle_of_expansion`. This is OpenAI's theorem `long_cycle_of_vertex_expansion` in `lean/OAI/Combinatorics/CycleDecomposition/ExpansionBoxes.lean`, with OpenAI's definitions `VertexExpansion` and `externalNeighbors` written out, so that the statement uses only Mathlib. The vertex type lives in an arbitrary universe (`Type cycleUniverse1`).
-- source:
--   The depth-first-search method for long paths and cycles in expanding graphs (S. Ben-Eliezer, M. Krivelevich and B. Sudakov, J. Combin. Theory Ser. B 102 (2012); surveyed in M. Krivelevich, Long paths and Hamiltonicity in random graphs, in Random Graphs, Geometry and Asymptotic Structure, London Math. Soc. Student Texts 84, Cambridge Univ. Press, 2016). Lean proof: OpenAI, A linear cycle-and-edge decomposition of every graph, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 181; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CycleDecomposition/ExpansionBoxes.lean (declaration OAI.ErdosGallai.Scale.long_cycle_of_vertex_expansion, stated here with its definition written out)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
open Finset SimpleGraph
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

theorem long_cycle_of_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hexp : ∀ U : Finset V, U.Nonempty → 2 * U.card ≤ Fintype.card V →
      α * U.card ≤ ((Finset.univ.filter (fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v)).card : ℝ))
    (hq : 1 ≤ α^2 * Fintype.card V / 100) :
    ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧
      α^2 * Fintype.card V / 100 < (c.length : ℝ) := by
  sorry

end ErdosGallai.Scale

end
end
end

end OAI
end
