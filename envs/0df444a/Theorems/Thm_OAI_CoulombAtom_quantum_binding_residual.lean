-- Prove2me | Theorems.Thm_OAI_CoulombAtom_quantum_binding_residual
-- name    : OAI.CoulombAtom.quantum_binding_residual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:40:23.383414+00:00
-- url     : https://prove2.me/theorems/1492715a-a5de-4e17-ba51-9e17759474a2
-- title:
--   OAI.CoulombAtom.quantum_binding_residual: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.quantum_binding_residual` of [lean/OAI/Analysis/CoulombIonization/Variational/BindingResidual.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Variational/BindingResidual.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter`, `open scoped Topology BigOperators InnerProductSpace`):
--
--   ```lean
--   lemma quantum_binding_residual {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
--       (F : fermionGraph (N+1)) (hstep : energy Z (N+1)+lam ≤ energy Z N)
--       {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
--       (∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)))+
--         lam*weightedMass F (bindingTotalMultiplier hR hε).value ≤
--       Z*(∑ i,weightedNuclear F i (fun x => bindingWeight R ε (x i)))+
--         (⟪(bindingTotalMultiplier hR hε).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.fermionGraph_innerProductSpace`, `OAI.CoulombAtom.fermionGraph_normedAddCommGroup`, `OAI.CoulombAtom.sectorDirections`, `OAI.CoulombAtom.weakGraph`, `OAI.CoulombAtom.FermionMultiplier.apply`, `OAI.CoulombAtom.FermionMultiplier` and `OAI.CoulombAtom.SmoothMultiplier` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.sectorExcessOperator` (definitions bundle `OAIQ071C004` of this split); `OAI.CoulombAtom.bindingWeight`, `OAI.CoulombAtom.weightedMass`, `OAI.CoulombAtom.weightedNuclear` and `OAI.CoulombAtom.weightedPairs` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombAtom.bindingTotalMultiplier` (definitions bundle `OAIQ071C008` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space`, `OAI.CoulombAtom.Spins` and `OAI.CoulombAtom.energy` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proof of `OAI.CoulombAtom.quantum_positive_price_binding_bound` of this split imports it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Variational/BindingResidual.lean (declaration OAI.CoulombAtom.quantum_binding_residual)

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C008

section

attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  bindingTotalMultiplier graphNuclear sectorExcessOperator
  weightedMass weightedPairs weightedNuclear weightedCoreDensity

lemma quantum_binding_residual {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph (N+1)) (hstep : energy Z (N+1)+lam ≤ energy Z N)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    (∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)))+
      lam*weightedMass F (bindingTotalMultiplier hR hε).value ≤
    Z*(∑ i,weightedNuclear F i (fun x => bindingWeight R ε (x i)))+
      (⟪(bindingTotalMultiplier hR hε).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re := by
  sorry

end CoulombAtom

end

end OAI
end
