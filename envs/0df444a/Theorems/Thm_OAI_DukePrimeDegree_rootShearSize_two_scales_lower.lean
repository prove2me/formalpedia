-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_rootShearSize_two_scales_lower
-- name    : OAI.DukePrimeDegree.rootShearSize_two_scales_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:41:23.915892+00:00
-- url     : https://prove2.me/theorems/9c2d87b8-fa97-4e33-ae77-e4676dc2e091
-- title:
--   OAI.DukePrimeDegree.rootShearSize_two_scales_lower: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.rootShearSize_two_scales_lower` of [lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/ShearingTwoAnnuli.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/ShearingTwoAnnuli.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Set Filter`, `open scoped BigOperators Topology`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem rootShearSize_two_scales_lower {n : ℕ} {i j : Fin n} (hij : i ≠ j)
--       (g : G n) (hk : 0 < rootShearingKappa i j g) (r s ρ : ℝ)
--       (hρ : 0 < ρ) (hρone : ρ ≤ 1)
--       (hrlo : ρ ≤ |rootShearingKappa i j g * r|)
--       (hrhi : |rootShearingKappa i j g * r| ≤ 1)
--       (hslo : 16 / ρ ≤ |rootShearingKappa i j g * s|) :
--       ρ / (16 * (n : ℝ)) ≤ rootShearSize hij g r ∨
--       ρ / (16 * (n : ℝ)) ≤ rootShearSize hij g s
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.rootShearSize` and `OAI.DukePrimeDegree.rootShearingKappa` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.G` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.exists_distinct_equal_leaf_horospherical_pair` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/ShearingTwoAnnuli.lean (declaration OAI.DukePrimeDegree.rootShearSize_two_scales_lower)

import Mathlib
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023

section

attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootShearSize_two_scales_lower {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hk : 0 < rootShearingKappa i j g) (r s ρ : ℝ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hrlo : ρ ≤ |rootShearingKappa i j g * r|)
    (hrhi : |rootShearingKappa i j g * r| ≤ 1)
    (hslo : 16 / ρ ≤ |rootShearingKappa i j g * s|) :
    ρ / (16 * (n : ℝ)) ≤ rootShearSize hij g r ∨
    ρ / (16 * (n : ℝ)) ≤ rootShearSize hij g s := by
  sorry

end DukePrimeDegree

end

end OAI
end
