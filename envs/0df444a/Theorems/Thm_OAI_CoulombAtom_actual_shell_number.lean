-- Prove2me | Theorems.Thm_OAI_CoulombAtom_actual_shell_number
-- name    : OAI.CoulombAtom.actual_shell_number
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:29:49.824986+00:00
-- url     : https://prove2.me/theorems/533f64ee-c16f-4af2-8eca-a58f1f932c8b
-- title:
--   OAI.CoulombAtom.actual_shell_number: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.actual_shell_number` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/ShellAbsorptionNumerics.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/ShellAbsorptionNumerics.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter`, `open scoped BigOperators InnerProductSpace`):
--
--   ```lean
--    theorem actual_shell_number {Z s u : ℝ} {N : ℕ} (hZ : 0 ≤ Z)
--       (hs : 0 < s) (hs1 : s ≤ 1) (hu : actualShellRadius*s ≤ u)
--       (hN : PriceMinimizes (energy Z) (1/s^4) (N+1))
--       (F : fermionGraph (N+1)) (p : SmoothMultiplier spaceDirections)
--       (hc : HasCompactSupport p.value)
--       (hp : ∀ y, p.value y ≠ 0 → u/2 ≤ ‖y‖ ∧ ‖y‖ ≤ 4*u) :
--       (1/s^4)*weightedMass F (oneBodySquareTotal p).value ≤ oneBodyGradientError p F+
--         2*(⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.SmoothMultiplier`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.fermionGraph_innerProductSpace`, `OAI.CoulombAtom.fermionGraph_normedAddCommGroup`, `OAI.CoulombAtom.sectorDirections`, `OAI.CoulombAtom.weakGraph`, `OAI.CoulombAtom.FermionMultiplier.apply` and `OAI.CoulombAtom.FermionMultiplier` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.PriceMinimizes` (definitions bundle `OAIQ071C001` of this split); `OAI.CoulombAtom.sectorExcessOperator` and `OAI.CoulombAtom.spaceDirections` (definitions bundle `OAIQ071C004` of this split); `OAI.CoulombAtom.weightedMass` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombAtom.oneBodyGradientError` and `OAI.CoulombAtom.oneBodySquareTotal` (definitions bundle `OAIQ071C008` of this split); `OAI.CoulombAtom.actualShellRadius` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space`, `OAI.CoulombAtom.Spins` and `OAI.CoulombAtom.energy` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI_CoulombAtom_actual_exterior_number_absorbed` and `OAI.CoulombAtom.exists_own_state_exterior_number` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/ShellAbsorptionNumerics.lean (declaration OAI.CoulombAtom.actual_shell_number)

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010

section

attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply FermionLipschitzMultiplier.apply oneBodySquareTotal
  formEnergy energy sectorExcessOperator fermionGraphValue shellBiasMultiplier
  rawFormPair formMass weightedMass oneBodyGradientError corePriceExcess shellMeanField innerScale

 theorem actual_shell_number {Z s u : ℝ} {N : ℕ} (hZ : 0 ≤ Z)
    (hs : 0 < s) (hs1 : s ≤ 1) (hu : actualShellRadius*s ≤ u)
    (hN : PriceMinimizes (energy Z) (1/s^4) (N+1))
    (F : fermionGraph (N+1)) (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value)
    (hp : ∀ y, p.value y ≠ 0 → u/2 ≤ ‖y‖ ∧ ‖y‖ ≤ 4*u) :
    (1/s^4)*weightedMass F (oneBodySquareTotal p).value ≤ oneBodyGradientError p F+
      2*(⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re := by
  sorry

end CoulombAtom

end

end OAI
end
