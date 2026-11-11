-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_approximate_moves_contradiction
-- name    : OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:17:01.521126+00:00
-- url     : https://prove2.me/theorems/5e308849-0189-4eaf-9b37-6452f395bf44
-- title:
--   OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction` of [lean/OAI/Probability/CriticalPercolation/Gluing/ApproximateMoveEndgame.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Gluing/ApproximateMoveEndgame.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set Function MeasureTheory ProbabilityTheory`, `open scoped Classical ENNReal`, `open Corridor`):
--
--   ```lean
--   theorem approximate_moves_contradiction
--       (hconnected : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (hpc : 0<(G.criticalProbability : ℝ)) (hpc1 : (G.criticalProbability : ℝ)<1)
--       (hmoves : ∀ e eta : ℝ, 0<e → e<1/10 → 0<eta → eta<1/10 →
--         ∃ m : ℕ, ∀ rho : ℝ, 0 < rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
--           (G.criticalProbability : ℝ)/2≤p ∧ p<G.criticalProbability ∧
--           (∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ rho) ∧
--           (∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ rho) ∧
--           ∀ y s, |s|=1 → 1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
--             (G.coordinateMove t z m e y s)) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BernoulliProduct.law` and `OAI.CriticalPercolation.BondGraph.coordinateMove` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.criticalProbability` and `OAI.CriticalPercolation.BondGraph.fullGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient` and `OAI.CriticalPercolation.BondGraph.critical_strip_null` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Gluing/ApproximateMoveEndgame.lean (declaration OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction)

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Corridor

variable {V E : Type*} (G : BondGraph V E)

theorem approximate_moves_contradiction
    (hconnected : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : 0<(G.criticalProbability : ℝ)) (hpc1 : (G.criticalProbability : ℝ)<1)
    (hmoves : ∀ e eta : ℝ, 0<e → e<1/10 → 0<eta → eta<1/10 →
      ∃ m : ℕ, ∀ rho : ℝ, 0 < rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
        (G.criticalProbability : ℝ)/2≤p ∧ p<G.criticalProbability ∧
        (∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ rho) ∧
        (∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ rho) ∧
        ∀ y s, |s|=1 → 1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
          (G.coordinateMove t z m e y s)) : False := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
