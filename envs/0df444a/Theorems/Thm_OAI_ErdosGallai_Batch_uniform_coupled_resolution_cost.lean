-- Prove2me | Theorems.Thm_OAI_ErdosGallai_Batch_uniform_coupled_resolution_cost
-- name    : OAI.ErdosGallai.Batch.uniform_coupled_resolution_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:06:00.376932+00:00
-- url     : https://prove2.me/theorems/6c77326c-1cf1-4990-b2e2-c2b42198825b
-- title:
--   Cost of resolving a batch of sparse pieces through coupled expanding routers (OpenAI, Erdős–Gallai decomposition)
-- statement:
--   This is a technical step of the proof. Write $\mathrm{cost}(G)$ = `decompositionCost G` for the least number of cycles and single edges into which the edges of $G$ can be partitioned. The lemma gives a constant $D_0 > 1$ such that the following holds for all $D \ge D_0$.
--
--   Let $G$ be a graph whose edges are split into a remainder $F$ and router graphs $R_r$. Each $R_r$ is supported on a vertex set $U_r$ with $D^{9/10} \le |U_r| \le D^{51/50}$, the $U_r$ are pairwise disjoint, and each $R_r$ is a cut expander on $U_r$ with constant $D^{9/10}$ (`CutExpansionOn`). Let the remainder $F$ be split into pieces $J_b$ supported on sets $W_b$ with $|W_b| \le D^{3/10}$. Inside each $W_b$, let there be disjoint sets $X_{b,i} \subseteq U_{r(b,i)}$ satisfying three conditions:
--   - they consist of vertices of $F$-degree at most $D^{1/100}$;
--   - each has at least $\max(8, D^{1/50})$ vertices;
--   - they satisfy the remaining hypotheses exactly as in the Lean statement.
--
--   Suppose every graph on fewer than $n$ vertices and at most $D^{3/10}$ vertices has cost at most $t$ times its number of vertices, and suppose $|W_b| < n$ for all $b$. Then there are subgraphs $H_r \le R_r$, each still a cut expander on $U_r$ with constant $D^{9/10}/4$, such that
--   $$\mathrm{cost}(G) \;\le\; t\Bigl(\sum_b |W_b| - \sum_{b,i} \bigl\lfloor |X_{b,i}|/2 \bigr\rfloor\Bigr) + 8\sum_{b,i} |X_{b,i}| + \sum_r \mathrm{cost}(H_r).$$
--
--   `decompositionCost`, `CutExpansionOn` and the other named functions come from the definitions bundle `OAIQWEGC000` of this split and the published bundle `Def_CycleDecomposition`. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.ErdosGallai.Batch.uniform_coupled_resolution_cost`, OpenAI's theorem of that name in `lean/OAI/Combinatorics/CycleDecomposition/CoupledResolution.lean`.
-- source:
--   OpenAI, A linear cycle-and-edge decomposition of every graph, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 181; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CycleDecomposition/CoupledResolution.lean (declaration OAI.ErdosGallai.Batch.uniform_coupled_resolution_cost)

import Mathlib
import Definitions.Def_OAIQWEGC000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

theorem uniform_coupled_resolution_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
    ∀ (V A B : Type) [Fintype V] [Fintype A] [Fintype B],
    ∀ (G F : SimpleGraph V) (R : A → SimpleGraph V) (U : A → Finset V),
    F ≤ G → (∀ r, R r ≤ G) →
    Pairwise (fun r s => Disjoint (R r).edgeSet (R s).edgeSet) →
    Pairwise (fun r s => Disjoint (U r) (U s)) →
    (∀ r, ∀ ⦃x y⦄, (R r).Adj x y → x ∈ U r ∧ y ∈ U r) →
    (∀ r, Disjoint F.edgeSet (R r).edgeSet) →
    F.edgeSet ∪ (⋃ r, (R r).edgeSet) = G.edgeSet →
    (∀ r, CutExpansionOn (R r) (U r) (D^(9/10:ℝ))) →
    (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
    ∀ (J : B → SimpleGraph V) (W : B → Finset V),
    (∀ b, J b ≤ F) → Pairwise (fun b c => Disjoint (J b).edgeSet (J c).edgeSet) →
    (⋃ b, (J b).edgeSet) = F.edgeSet →
    (∀ b, ∀ ⦃x y⦄, (J b).Adj x y → x ∈ W b ∧ y ∈ W b) →
    (∀ b, ((W b).card:ℝ) ≤ D^(3/10:ℝ)) →
    ∀ (I : B → Type) [∀ b, Fintype (I b)] (X : ∀ b, I b → Finset V)
      (_hXd : ∀ b, Pairwise fun i j => Disjoint (X b i) (X b j)),
    (∀ b i, X b i ⊆ W b) →
    ∀ rX : ∀ b, I b → A,
    (∀ b i, X b i ⊆ U (rX b i)) →
    (∀ b i v, v ∈ X b i → (F.degree v:ℝ) ≤ D^(1/100:ℝ)) →
    1 ≤ D^(1/100:ℝ) → (∀ b i, 8 ≤ (X b i).card) →
    (∀ b i, (D^(1/100:ℝ))^2 ≤ (X b i).card) →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → (∀ b, (W b).card < n) →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (Fintype.card Q:ℝ) ≤ D^(3/10:ℝ) → (decompositionCost H:ℝ) ≤ t * Fintype.card Q) →
    ∃ H : A → SimpleGraph V,
      (∀ r, H r ≤ R r) ∧
      (∀ r, CutExpansionOn (H r) (U r) (D^(9/10:ℝ)/4)) ∧
      (decompositionCost G:ℝ) ≤
        t * ((∑ b, ((W b).card:ℝ)) - ∑ b, ∑ i, ((X b i).card / 2:ℕ)) +
        8 * (∑ b, ∑ i, ((X b i).card:ℝ)) + ∑ r, (decompositionCost (H r):ℝ) := by
  sorry

end
end ErdosGallai.Batch

end
end
end

end OAI
end
