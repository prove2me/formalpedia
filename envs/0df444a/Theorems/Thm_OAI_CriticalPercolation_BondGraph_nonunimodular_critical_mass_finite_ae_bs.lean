-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_nonunimodular_critical_mass_finite_ae_bs
-- name    : OAI.CriticalPercolation.BondGraph.nonunimodular_critical_mass_finite_ae_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:26:15.839817+00:00
-- url     : https://prove2.me/theorems/d22fa819-5c29-4c25-8ed8-b3e4fbaa571a
-- title:
--   OAI.CriticalPercolation.BondGraph.nonunimodular_critical_mass_finite_ae_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.nonunimodular_critical_mass_finite_ae` of [lean/OAI/Probability/CriticalPercolation/Modular/CriticalHeavyNull.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/CriticalHeavyNull.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory`, `open scoped Classical ENNReal`):
--
--   ```lean
--   theorem nonunimodular_critical_mass_finite_ae_bs
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (hpc : G.criticalProbability<1) (hu : ¬G.CombinatoriallyUnimodular) (o : V) :
--       ∀ᵐ ω ∂G.law G.criticalProbability, ∀ v, G.modularMass o (G.cluster ω v)<∞
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.cluster`, `OAI.CriticalPercolation.BondGraph.criticalProbability`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law` and `OAI.CriticalPercolation.BondGraph.modularMass` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample_bs`, `OAI.CriticalPercolation.BondGraph.nonunimodular_critical_twoPoint_decay_bs` and `OAI.CriticalPercolation.BondGraph.nonunimodular_no_percolation_at_criticality_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/CriticalHeavyNull.lean (declaration OAI.CriticalPercolation.BondGraph.nonunimodular_critical_mass_finite_ae)

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
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem nonunimodular_critical_mass_finite_ae_bs
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (hu : ¬G.CombinatoriallyUnimodular) (o : V) :
    ∀ᵐ ω ∂G.law G.criticalProbability, ∀ v, G.modularMass o (G.cluster ω v)<∞ := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
