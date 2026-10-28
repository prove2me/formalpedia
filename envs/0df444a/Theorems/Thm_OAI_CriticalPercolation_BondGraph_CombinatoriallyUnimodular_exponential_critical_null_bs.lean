-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_CombinatoriallyUnimodular_exponential_critical_null_bs
-- name    : OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular.exponential_critical_null_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:20:37.475473+00:00
-- url     : https://prove2.me/theorems/98abfdd8-476e-4654-b721-2a5aebbd3e4a
-- title:
--   OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular.exponential_critical_null_bs (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular.exponential_critical_null` of [lean/OAI/Probability/CriticalPercolation/Modular/UnimodularGeometric.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/UnimodularGeometric.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem CombinatoriallyUnimodular.exponential_critical_null_bs
--       (hu : G.CombinatoriallyUnimodular) (hc : G.fullGraph.Connected)
--       (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (hpc : G.criticalProbability < 1)
--       (o : V) (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
--       (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ)) :
--       G.law G.criticalProbability G.percolates = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.criticalProbability`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law`, `OAI.CriticalPercolation.BondGraph.percolates` and `OAI.CriticalPercolation.BondGraph.vertexBall` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.main_light_or_sparse_polynomial_boundary_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/UnimodularGeometric.lean (declaration OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular.exponential_critical_null)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem CombinatoriallyUnimodular.exponential_critical_null_bs
    (hu : G.CombinatoriallyUnimodular) (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (hpc : G.criticalProbability < 1)
    (o : V) (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ)) :
    G.law G.criticalProbability G.percolates = 0 := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
