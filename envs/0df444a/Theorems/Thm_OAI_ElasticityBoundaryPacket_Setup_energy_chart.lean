-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryPacket_Setup_energy_chart
-- name    : OAI.ElasticityBoundaryPacket.Setup.energy_chart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:38:07.088679+00:00
-- url     : https://prove2.me/theorems/c97da179-544d-4573-8a49-fe14144c6395
-- title:
--   OAI.ElasticityBoundaryPacket.Setup.energy_chart: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryPacket.Setup.energy_chart` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryPacket`, with `open Set Filter MeasureTheory`, `open scoped Topology BigOperators`, `open Elasticity ElasticityBoundaryDensityPull ElasticityBoundaryPacketMass ElasticityBoundaryPhysicalMass ElasticityBoundaryCutoffLayer`):
--
--   ```lean
--   lemma Setup.energy_chart (s : Setup Ω x) (hΩ : MeasurableSet Ω) {l m : X → ℝ}
--       (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m) (p q : Polynomial W) (δ : ℝ) :
--       complexTrialEnergy l m (s.trial p δ) (s.trial q δ)=
--         ∫ y in ElasticityBoundaryProfileBounds.halfspace,
--           tensorDensity (fun i α j β => s.rawCoeff (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y)
--             (fun i α => dpart (cutoffLayer s.cutoff p δ i) α y)
--             (fun i α => dpart (cutoffLayer s.cutoff q δ i) α y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Elasticity.BoundedCoefficient`, `OAI.Elasticity.complexTrialEnergy` and `OAI.Elasticity.tensorDensity` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityBoundaryCutoffLayer.cutoffLayer`, `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryPacket.I`, `OAI.ElasticityBoundaryPacket.Setup`, `OAI.ElasticityBoundaryPacket.X`, `OAI.ElasticityBoundaryProfileBounds.Y`, `OAI.ElasticityBoundaryProfileBounds.halfspace`, `OAI.ElasticityBoundaryStrongLayer.dpart` and `OAI.ElasticityBoundaryPacket.Setup.rawCoeff` (definitions bundle `OAIQ6El001` of this split); `OAI.ElasticityBoundaryPacket.Setup.trial` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryPacket.Setup.extract_normal` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryEnergy.lean (declaration OAI.ElasticityBoundaryPacket.Setup.energy_chart)

import Mathlib
import Definitions.Def_OAIQ6El004

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryPacket

open Set Filter MeasureTheory
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryDensityPull ElasticityBoundaryPacketMass ElasticityBoundaryPhysicalMass ElasticityBoundaryCutoffLayer
  ElasticityBoundaryStrongLayer ElasticityBoundaryMixedScaling ElasticityBoundaryGradientTransfer
  ElasticityBoundaryChartOperator ElasticityBoundaryMVNormal ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryCutoffParametrix ElasticityBoundaryActualTower

variable {Ω : Set X} {x : X}

lemma Setup.energy_chart (s : Setup Ω x) (hΩ : MeasurableSet Ω) {l m : X → ℝ}
    (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m) (p q : Polynomial W) (δ : ℝ) :
    complexTrialEnergy l m (s.trial p δ) (s.trial q δ)=
      ∫ y in ElasticityBoundaryProfileBounds.halfspace,
        tensorDensity (fun i α j β => s.rawCoeff (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y)
          (fun i α => dpart (cutoffLayer s.cutoff p δ i) α y)
          (fun i α => dpart (cutoffLayer s.cutoff q δ i) α y) := by
  sorry

end ElasticityBoundaryPacket

end

end OAI
end
