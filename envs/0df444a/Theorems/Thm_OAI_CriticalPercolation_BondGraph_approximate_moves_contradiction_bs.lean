-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_approximate_moves_contradiction_bs
-- name    : OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:21:25.595586+00:00
-- url     : https://prove2.me/theorems/496fa218-537d-425f-b778-42a006e96d98
-- title:
--   OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction` of [lean/OAI/Probability/CriticalPercolation/Gluing/ApproximateMoveEndgame.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Gluing/ApproximateMoveEndgame.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set Function MeasureTheory ProbabilityTheory`, `open scoped Classical ENNReal`, `open Corridor`):
--
--   ```lean
--   theorem approximate_moves_contradiction_bs
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
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BernoulliProduct.law`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.coordinateMove`, `OAI.CriticalPercolation.BondGraph.criticalProbability` and `OAI.CriticalPercolation.BondGraph.fullGraph` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.critical_strip_null_bs` and `OAI.CriticalPercolation.BondGraph.ellipse_critical_contradiction_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Gluing/ApproximateMoveEndgame.lean (declaration OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction)

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
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Corridor

variable {V E : Type*} (G : BondGraph V E)

theorem approximate_moves_contradiction_bs
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
