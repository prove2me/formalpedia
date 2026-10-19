-- Prove2me | Theorems.Thm_OAI_ErdosGallai_Scale_uniform_local_box_cost
-- name    : OAI.ErdosGallai.Scale.uniform_local_box_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:05:55.619992+00:00
-- url     : https://prove2.me/theorems/f5128cfb-717e-44d6-9364-3080c59cf0d1
-- title:
--   Cost bound for a local box of light pieces and expanding pieces (OpenAI, Erdős–Gallai decomposition)
-- statement:
--   This is a technical step of the proof. There is a constant $D_0 > 1$ such that the following holds for all $D \ge D_0$ and $w_{\min}$ with `MainScaleReady wmin D`.
--
--   Let $L$ and $A$ be lists of assigned pieces whose graphs partition the edges of their union (`GraphPartition`). All the pieces lie in a box $Y$ with $|Y| \le D^{51/50}$, and the pieces of $L$ cover $Y$. Assume:
--   - the pieces of $A$ are vertex-disjoint expanders, with $D^{9/10} \le |R.\mathrm{vertices}| \le D^{51/50}$ and `CutExpansionOn R.graph R.vertices (D^(9/10))`;
--   - the pieces of $L$ are small and sparse, with at most $D^{1/1000}$ vertices and average degree at most $D^{1/1000}$;
--   - the total vertex mass of $L$ is at most $2|Y|$.
--
--   Assume two induction hypotheses for all graphs on fewer than $n$ vertices, where $|Y| \le n$ and $D^{3/10} < n$:
--   - their decomposition cost is at most $C$ times their number of vertices;
--   - if they also have at most $D^{3/10}$ vertices, their batch cost `Batch.decompositionCost` is at most $t$ times their number of vertices.
--
--   Then the decomposition cost of the union of all the pieces is at most
--   $$(9 + C\eta)\,m(A) + (t+8)\,m(L) + (8 - t/3)\,m(A) + \Bigl(\frac{2t/3}{\log_2 D} - 8\Bigr)|Y|,$$
--   where $m$ = `vertexMass` is the total number of vertices counted over pieces, and $\eta$ = `mainEta`.
--
--   The named functions come from the definitions bundle `OAIQWEGC000` of this split and the published bundle `Def_CycleDecomposition`. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.ErdosGallai.Scale.uniform_local_box_cost`, OpenAI's theorem of that name in `lean/OAI/Combinatorics/CycleDecomposition/LayerCosts.lean`.
-- source:
--   OpenAI, A linear cycle-and-edge decomposition of every graph, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 181; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CycleDecomposition/LayerCosts.lean (declaration OAI.ErdosGallai.Scale.uniform_local_box_cost)

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

theorem uniform_local_box_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ wmin : ℝ,
    ErdosGallai.MainScaleReady wmin D →
    ∀ (V : Type) [Fintype V] (L A : List (AssignedPiece V)) (Y : Finset V),
    GraphPartition (graphUnion (L.map AssignedPiece.graph ++ A.map AssignedPiece.graph))
      (L.map AssignedPiece.graph ++ A.map AssignedPiece.graph) →
    A.Pairwise (fun R S => Disjoint R.vertices S.vertices) →
    (∀ R ∈ A, R.vertices ⊆ Y) →
    (∀ Q ∈ L, Q.vertices ⊆ Y) →
    (∀ v ∈ Y, ∃ Q ∈ L, v ∈ Q.vertices) →
    (∀ Q ∈ L, Q.vertices.Nonempty ∧ (Q.vertices.card:ℝ) ≤ D^(1/1000:ℝ) ∧
      2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ D^(1/1000:ℝ)) →
    (∀ R ∈ A, D^(9/10:ℝ) ≤ (R.vertices.card:ℝ) ∧ (R.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
      CutExpansionOn R.graph R.vertices (D^(9/10:ℝ))) →
    (Y.card:ℝ) ≤ D^(51/50:ℝ) → vertexMass L ≤ 2*Y.card →
    ∀ (n : ℕ) (C t : ℝ), 0 ≤ C → 0 ≤ t → Y.card ≤ n → D^(3/10:ℝ) < n →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (ErdosGallai.decompositionCost H:ℝ) ≤ C*Fintype.card Q) →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (Fintype.card Q:ℝ) ≤ D^(3/10:ℝ) → (Batch.decompositionCost H:ℝ) ≤ t*Fintype.card Q) →
    (decompositionCost (graphUnion (L.map AssignedPiece.graph ++ A.map AssignedPiece.graph)):ℝ) ≤
      (9+C*ErdosGallai.mainEta)*vertexMass A + (t+8)*vertexMass L +
      (8-t/3)*vertexMass A + ((2/3)*t/logb 2 D-8)*Y.card := by
  sorry

end
end ErdosGallai.Scale

end

end
end

end OAI
end
