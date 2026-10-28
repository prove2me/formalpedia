-- Prove2me | Theorems.Thm_OAI_CoulombAtom_binding_form_lower
-- name    : OAI.CoulombAtom.binding_form_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:40:16.540221+00:00
-- url     : https://prove2.me/theorems/370454e5-3cf3-4c1f-a2fb-ca971dffa2f9
-- title:
--   OAI.CoulombAtom.binding_form_lower: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.binding_form_lower` of [lean/OAI/Analysis/CoulombIonization/Variational/WeightedMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Variational/WeightedMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Filter`, `open scoped Topology BigOperators InnerProductSpace`, `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff InnerProductSpace`, `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff InnerProductSpace`, `open MeasureTheory Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Filter`, `open scoped Topology BigOperators InnerProductSpace`, `open MeasureTheory Filter`, `open scoped Topology BigOperators InnerProductSpace`, `open MeasureTheory Filter`, `open scoped Topology BigOperators InnerProductSpace`, `open MeasureTheory Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Filter`, `open scoped Topology BigOperators InnerProductSpace`, `open MeasureTheory Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Filter`, `open scoped Topology BigOperators InnerProductSpace`, `open MeasureTheory Filter`, `open scoped Topology BigOperators InnerProductSpace`, `open MeasureTheory Filter`, `open scoped Topology BigOperators InnerProductSpace`):
--
--   ```lean
--   lemma binding_form_lower {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
--       (Z : ℝ) (F : fermionGraph N) :
--       (∑ i : Fin N, (weightedCoreDensity Z F i (fun x => bindingWeight R ε (x i)) -
--         Z * weightedNuclear F i (fun x => bindingWeight R ε (x i)) +
--         weightedPairs F i (fun x => bindingWeight R ε (x i)))) ≤
--         (⟪(bindingTotalMultiplier hR hε).apply F, coulombFormOperator Z N F⟫_ℂ).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.coulombFormOperator`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.fermionGraph_innerProductSpace`, `OAI.CoulombAtom.fermionGraph_normedAddCommGroup`, `OAI.CoulombAtom.sectorDirections`, `OAI.CoulombAtom.weakGraph` and `OAI.CoulombAtom.FermionMultiplier.apply` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.bindingWeight`, `OAI.CoulombAtom.weightedCoreDensity`, `OAI.CoulombAtom.weightedNuclear` and `OAI.CoulombAtom.weightedPairs` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombAtom.bindingTotalMultiplier` (definitions bundle `OAIQ071C008` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space` and `OAI.CoulombAtom.Spins` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proof of `OAI.CoulombAtom.quantum_binding_residual` of this split imports it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Variational/WeightedMass.lean (declaration OAI.CoulombAtom.binding_form_lower)

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
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply coulombFormOperator fermionGraph weakGraph fermionGraphValue

attribute [local irreducible] bindingTotalMultiplier graphNuclear graphPair
  weightedMass weightedGradient weightedFullDensity weightedCoreDensity weightedNuclear weightedPairs

attribute [local irreducible] weightedKinetic graphKineticPair

lemma binding_form_lower {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (Z : ℝ) (F : fermionGraph N) :
    (∑ i : Fin N, (weightedCoreDensity Z F i (fun x => bindingWeight R ε (x i)) -
      Z * weightedNuclear F i (fun x => bindingWeight R ε (x i)) +
      weightedPairs F i (fun x => bindingWeight R ε (x i)))) ≤
      (⟪(bindingTotalMultiplier hR hε).apply F, coulombFormOperator Z N F⟫_ℂ).re := by
  sorry

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end

end OAI
end
