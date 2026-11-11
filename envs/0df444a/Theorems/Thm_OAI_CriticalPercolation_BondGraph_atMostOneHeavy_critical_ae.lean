-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_atMostOneHeavy_critical_ae
-- name    : OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:17:18.968722+00:00
-- url     : https://prove2.me/theorems/ce76ba07-16af-4d88-ace2-878bcb094980
-- title:
--   OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae` of [lean/OAI/Probability/CriticalPercolation/Modular/CriticalHeavyUniqueness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/CriticalHeavyUniqueness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory Filter`, `open scoped Classical ENNReal`):
--
--   ```lean
--   theorem atMostOneHeavy_critical_ae (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (hq : G.QuasiTransitive) (hp1 : G.criticalProbability<1) (o : V) :
--       ∀ᵐ ω ∂G.law G.criticalProbability, ω∈G.atMostOneHeavy o
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph.atMostOneHeavy` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.criticalProbability`, `OAI.CriticalPercolation.BondGraph.fullGraph` and `OAI.CriticalPercolation.BondGraph.law` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.main_all_light_or_sparse_boundary` and `OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Modular/CriticalHeavyUniqueness.lean (declaration OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae)

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem atMostOneHeavy_critical_ae (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hp1 : G.criticalProbability<1) (o : V) :
    ∀ᵐ ω ∂G.law G.criticalProbability, ω∈G.atMostOneHeavy o := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
