-- Prove2me | Theorems.Thm_OAI_CoulombAtom_ordinaryDensity_global_unshifted
-- name    : OAI.CoulombAtom.ordinaryDensity_global_unshifted
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:32:47.292053+00:00
-- url     : https://prove2.me/theorems/0cef04b4-5fff-4fd5-be0c-19c3231fb427
-- title:
--   OAI.CoulombAtom.ordinaryDensity_global_unshifted: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.ordinaryDensity_global_unshifted` of [lean/OAI/Analysis/CoulombIonization/Localization/BarrierOrdinaryGlobalBarrier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Localization/BarrierOrdinaryGlobalBarrier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter Set`, `open scoped BigOperators ENNReal`):
--
--   ```lean
--   theorem ordinaryDensity_global_unshifted {N : ℕ} {Z δ : ℝ}
--       (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hN : (N:ℝ) ≤ 3*Z)
--       (ψ : FormVector N) (hψ : FormAdmissible ψ)
--       (he : formEnergy Z ψ ≤ allSectorEnergy Z+δ) :
--       (∫ x, (ordinaryDensity ψ x)^(5/3:ℝ)) ≤
--         Pauli.globalDensityConstant*(Z^(7/3:ℝ)+δ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.allSectorEnergy` and `OAI.CoulombAtom.Pauli.globalDensityConstant` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombAtom.ordinaryDensity` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.FormAdmissible`, `OAI.CoulombAtom.FormVector`, `OAI.CoulombAtom.Space` and `OAI.CoulombAtom.formEnergy` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proof of `OAI.CoulombAtom.normalized_inner_event_global_bound` of this split imports it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Localization/BarrierOrdinaryGlobalBarrier.lean (declaration OAI.CoulombAtom.ordinaryDensity_global_unshifted)

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010

section

attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom

theorem ordinaryDensity_global_unshifted {N : ℕ} {Z δ : ℝ}
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hN : (N:ℝ) ≤ 3*Z)
    (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (he : formEnergy Z ψ ≤ allSectorEnergy Z+δ) :
    (∫ x, (ordinaryDensity ψ x)^(5/3:ℝ)) ≤
      Pauli.globalDensityConstant*(Z^(7/3:ℝ)+δ) := by
  sorry

end CoulombAtom

end

end OAI
end
