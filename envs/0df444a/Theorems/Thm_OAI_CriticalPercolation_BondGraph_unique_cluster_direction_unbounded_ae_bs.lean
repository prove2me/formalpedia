-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_unique_cluster_direction_unbounded_ae_bs
-- name    : OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:29:51.264252+00:00
-- url     : https://prove2.me/theorems/5d94e6f7-3767-45cf-8976-ee81e1777799
-- title:
--   OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae` of [lean/OAI/Probability/CriticalPercolation/Criticality/DirectionalTail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/DirectionalTail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set Function MeasureTheory ProbabilityTheory Filter`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem unique_cluster_direction_unbounded_ae_bs [Countable V] [Countable E]
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (hg : G.SubexponentialGrowth) (p : unitInterval)
--       (hp : (p : ℝ)∈Set.Ioo 0 1) (hpositive : 0<G.law p G.percolates)
--       (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v) :
--       ∀ᵐ ω ∂G.law p, ∀ v, (G.cluster ω v).Infinite →
--         ∀ n : ℕ, ∃ w∈G.cluster ω v, (n : ℝ)<f w
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.SubexponentialGrowth`, `OAI.CriticalPercolation.BondGraph.cluster`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law` and `OAI.CriticalPercolation.BondGraph.percolates` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.critical_strip_null_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/DirectionalTail.lean (declaration OAI.CriticalPercolation.BondGraph.unique_cluster_direction_unbounded_ae)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem unique_cluster_direction_unbounded_ae_bs [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (p : unitInterval)
    (hp : (p : ℝ)∈Set.Ioo 0 1) (hpositive : 0<G.law p G.percolates)
    (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v) :
    ∀ᵐ ω ∂G.law p, ∀ v, (G.cluster ω v).Infinite →
      ∀ n : ℕ, ∃ w∈G.cluster ω v, (n : ℝ)<f w := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
