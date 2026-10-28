-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_central_pair_regular_exists
-- name    : OAI.ScalarConductivity.central_pair_regular_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:41:49.921485+00:00
-- url     : https://prove2.me/theorems/f7276451-c0a4-430b-a633-3cee9c5b459d
-- title:
--   OAI.ScalarConductivity.central_pair_regular_exists: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.central_pair_regular_exists` of [lean/OAI/Analysis/Conductivity/Sobolev/CentralPairRegularity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Sobolev/CentralPairRegularity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open Set MeasureTheory Filter Topology`):
--
--   ```lean
--   theorem central_pair_regular_exists (s : Fin 3 → ℝ) :
--       ∃ p : Fin 2 → centralEnergySpace s,
--         (∀ j,centralM s (p j)=0) ∧
--         (∀ j,CentralVariationalEquation s (centralBasisSlopes j) (p j)) ∧
--         (∀ j,WeaklyHarmonicOn (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) centralHarmonicRegion) ∧
--         ∀ (a : R3) (R : ℝ),0<R → Metric.closedBall a R⊆centralHarmonicRegion →
--           (∀ j,AnalyticOnNhd ℝ
--             (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) (R/4)) (Metric.ball a (R/4)) ∧
--             (centralWholeL2 (centralAmbientComponent s 0 (p j).val) : R3 → ℝ)
--               =ᵐ[volume.restrict (Metric.ball a (R/4))]
--               radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) (R/4)) ∧
--           ∀ᵐ x∂volume,x∈Metric.ball a (R/4) → ∃ r>0,
--             Metric.ball x r⊆Metric.ball a (R/4) ∧
--             HarmonicPairRegularOn
--               (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p 0).val)) (R/4))
--               (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p 1).val)) (R/4))
--               (Metric.ball x r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Box3`, `OAI.ScalarConductivity.CentralAmbient`, `OAI.ScalarConductivity.CentralJets`, `OAI.ScalarConductivity.CentralL2`, `OAI.ScalarConductivity.CentralTraceFields`, `OAI.ScalarConductivity.SpectralJet`, `OAI.ScalarConductivity.SpectralL2`, `OAI.ScalarConductivity.centralBasisSlopes`, `OAI.ScalarConductivity.centralEnergySpace`, `OAI.ScalarConductivity.centralMeasure`, `OAI.ScalarConductivity.spectralTraceGraph` and `OAI.ScalarConductivity.torusRate` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.HarmonicPairRegularOn`, `OAI.ScalarConductivity.WeaklyHarmonicOn` and `OAI.ScalarConductivity.WeylSpace` (definitions bundle `OAIQ059C001` of this split); `OAI.ScalarConductivity.CentralVariationalEquation`, `OAI.ScalarConductivity.centralAmbientComponent`, `OAI.ScalarConductivity.centralHarmonicRegion`, `OAI.ScalarConductivity.centralM` and `OAI.ScalarConductivity.centralWholeL2` (definitions bundle `OAIQ059C003` of this split); `OAI.ScalarConductivity.radialMollify` (definitions bundle `OAIQ059C005` of this split); `OAI.ScalarConductivity.R3` (the published bundle `Def_Conductivity`).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.physicalFiniteEndingData_nonempty` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Sobolev/CentralPairRegularity.lean (declaration OAI.ScalarConductivity.central_pair_regular_exists)

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C003
import Definitions.Def_OAIQ059C005

section

attribute [-instance] _root_.OAI.ScalarConductivity.H10_completeSpace _root_.OAI.ScalarConductivity.H1_completeSpace _root_.OAI.ScalarConductivity.H1_isClosed _root_.OAI.ScalarConductivity.ballMeasure_finite _root_.OAI.ScalarConductivity.bumpProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem central_pair_regular_exists (s : Fin 3 → ℝ) :
    ∃ p : Fin 2 → centralEnergySpace s,
      (∀ j,centralM s (p j)=0) ∧
      (∀ j,CentralVariationalEquation s (centralBasisSlopes j) (p j)) ∧
      (∀ j,WeaklyHarmonicOn (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) centralHarmonicRegion) ∧
      ∀ (a : R3) (R : ℝ),0<R → Metric.closedBall a R⊆centralHarmonicRegion →
        (∀ j,AnalyticOnNhd ℝ
          (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) (R/4)) (Metric.ball a (R/4)) ∧
          (centralWholeL2 (centralAmbientComponent s 0 (p j).val) : R3 → ℝ)
            =ᵐ[volume.restrict (Metric.ball a (R/4))]
            radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) (R/4)) ∧
        ∀ᵐ x∂volume,x∈Metric.ball a (R/4) → ∃ r>0,
          Metric.ball x r⊆Metric.ball a (R/4) ∧
          HarmonicPairRegularOn
            (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p 0).val)) (R/4))
            (radialMollify (centralWholeL2 (centralAmbientComponent s 0 (p 1).val)) (R/4))
            (Metric.ball x r) := by
  sorry

end ScalarConductivity

end
end

end OAI
end
