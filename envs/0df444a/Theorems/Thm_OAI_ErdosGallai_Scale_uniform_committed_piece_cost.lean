-- Prove2me | Theorems.Thm_OAI_ErdosGallai_Scale_uniform_committed_piece_cost
-- name    : OAI.ErdosGallai.Scale.uniform_committed_piece_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:06:06.925291+00:00
-- url     : https://prove2.me/theorems/6a90f443-1b12-4da9-9e98-82448c4c8cfc
-- title:
--   Cost bound for every committed piece of a layered scale decomposition (OpenAI, Erdős–Gallai decomposition)
-- statement:
--   This is a technical step of the proof. There is a constant $D_0 > 1$ such that the following holds for every $D_\star \ge D_0$ and every assigned piece $P$, meaning a vertex set together with a graph supported on it (`AssignedPiece`).
--
--   Let $H$ be a layered decomposition of $P$ at scale $D_\star$ (`Layers P Dstar`). Let $C \ge 0$ be a constant such that every graph on fewer than $|P.\mathrm{vertices}|$ vertices has decomposition cost at most $C$ times its number of vertices (induction hypothesis). Then for every $k \le$ `H.count`, every piece $R$ committed among the first $k$ levels (`R ∈ pastPieces H.system 0 k [P]`) satisfies
--   $$\mathrm{cost}(R.\mathrm{graph}) \;\le\; (9 + C\eta)\,|R.\mathrm{vertices}|,$$
--   where $\eta$ = `mainEta` is a fixed small constant and cost is `decompositionCost`.
--
--   The named functions come from the definitions bundle `OAIQWEGC000` of this split and the published bundle `Def_CycleDecomposition`. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.ErdosGallai.Scale.uniform_committed_piece_cost`, OpenAI's theorem of that name in `lean/OAI/Combinatorics/CycleDecomposition/LayerCosts.lean`.
-- source:
--   OpenAI, A linear cycle-and-edge decomposition of every graph, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 181; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CycleDecomposition/LayerCosts.lean (declaration OAI.ErdosGallai.Scale.uniform_committed_piece_cost)

import Mathlib
import Definitions.Def_OAIQWEGC000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset

section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem uniform_committed_piece_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ Dstar ≥ D₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (P : AssignedPiece V) (H : Layers P Dstar),
    ∀ (C : ℝ), 0 ≤ C →
    (∀ (Q : Type) [Fintype Q] (G : SimpleGraph Q), Fintype.card Q < P.vertices.card →
      (ErdosGallai.decompositionCost G:ℝ) ≤ C*Fintype.card Q) →
    ∀ k ≤ H.count, ∀ R ∈ pastPieces H.system 0 k [P],
      (decompositionCost R.graph:ℝ) ≤ (9+C*ErdosGallai.mainEta)*R.vertices.card := by
  sorry

end
end ErdosGallai.Scale

end

end
end

end OAI
end
