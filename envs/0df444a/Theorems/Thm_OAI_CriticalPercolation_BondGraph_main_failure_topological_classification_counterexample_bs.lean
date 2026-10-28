-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_main_failure_topological_classification_counterexample_bs
-- name    : OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:27:10.826154+00:00
-- url     : https://prove2.me/theorems/8541c9ed-7196-4964-8cd9-628da39dff3d
-- title:
--   OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample_bs (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample` of [lean/OAI/Probability/CriticalPercolation/GraphTopology/TopologicalClassificationBoundary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphTopology/TopologicalClassificationBoundary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set Function MeasureTheory Topology`, `open scoped Classical ENNReal Pointwise`):
--
--   ```lean
--   theorem main_failure_topological_classification_counterexample_bs [Infinite V]
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (hpc : G.criticalProbability<1)
--       (hper : G.law G.criticalProbability G.percolates≠0) (o : V) :
--       ∃ d : ℕ, 2≤d ∧ ∃ C : ℕ,
--         (G.orbitPower o (2*C+1)).Connected ∧
--         (MulAction.orbit G.Aut o).Infinite ∧
--         (∀ u, ((G.orbitPower o (2*C+1)).neighborSet u).Finite) ∧
--         (∀ u v, ∃ g : G.orbitPower o (2*C+1) ≃g G.orbitPower o (2*C+1), g u=v) ∧
--         (∀ R : ℕ, ∃ n≥R, ∀ u : MulAction.orbit G.Aut o,
--           (GraphTopology.reachBall (G.orbitPower o (2*C+1)) u n).ncard≤n^(d+1)) ∧
--         GraphTopology.HasUniformCompactApproximatePowers
--           (G.orbitPower o (2*C+1)) (5^(d+2)) ∧
--         ¬GraphTopology.HasCompactOpenVirtuallyNilpotentQuotient
--           (G.orbitPower o (2*C+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.Aut`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.criticalProbability`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.instGroupAut`, `OAI.CriticalPercolation.BondGraph.instMulActionAut`, `OAI.CriticalPercolation.BondGraph.law`, `OAI.CriticalPercolation.BondGraph.orbitPower` and `OAI.CriticalPercolation.BondGraph.percolates` (definitions bundle `OAIQ078B000` of this split); `OAI.CriticalPercolation.GraphTopology.HasCompactOpenVirtuallyNilpotentQuotient`, `OAI.CriticalPercolation.GraphTopology.HasUniformCompactApproximatePowers` and `OAI.CriticalPercolation.GraphTopology.reachBall` (definitions bundle `OAIQ078B001` of this split).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.critical_finite_general_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphTopology/TopologicalClassificationBoundary.lean (declaration OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample)

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function MeasureTheory Topology
open scoped Classical ENNReal Pointwise

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem main_failure_topological_classification_counterexample_bs [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1)
    (hper : G.law G.criticalProbability G.percolates≠0) (o : V) :
    ∃ d : ℕ, 2≤d ∧ ∃ C : ℕ,
      (G.orbitPower o (2*C+1)).Connected ∧
      (MulAction.orbit G.Aut o).Infinite ∧
      (∀ u, ((G.orbitPower o (2*C+1)).neighborSet u).Finite) ∧
      (∀ u v, ∃ g : G.orbitPower o (2*C+1) ≃g G.orbitPower o (2*C+1), g u=v) ∧
      (∀ R : ℕ, ∃ n≥R, ∀ u : MulAction.orbit G.Aut o,
        (GraphTopology.reachBall (G.orbitPower o (2*C+1)) u n).ncard≤n^(d+1)) ∧
      GraphTopology.HasUniformCompactApproximatePowers
        (G.orbitPower o (2*C+1)) (5^(d+2)) ∧
      ¬GraphTopology.HasCompactOpenVirtuallyNilpotentQuotient
        (G.orbitPower o (2*C+1)) := by
  sorry

end BondGraph
end CriticalPercolation
end
end

end OAI
end
