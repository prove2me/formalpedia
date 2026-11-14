-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_AnalyticGrowth_hasSum_realZeroPole
-- name    : OAI.PrimeDegreePackets.AnalyticGrowth.hasSum_realZeroPole
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:31:03.779202+00:00
-- url     : https://prove2.me/theorems/fe5478ab-6129-4a32-bb9d-683aed610f95
-- title:
--   OAI.PrimeDegreePackets.AnalyticGrowth.hasSum_realZeroPole: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.AnalyticGrowth.hasSum_realZeroPole` of [lean/OAI/NumberTheory/PrimePackets/ZeroReflection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/ZeroReflection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets.AnalyticGrowth`, with `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal`, `open MeasureTheory Filter Set Module`, `open scoped TensorProduct`, `open Set Module`, `open MeasureTheory Set`, `open scoped ENNReal`, `open IsDiscreteValuationRing IsLocalRing`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set IsDiscreteValuationRing`, `open Filter`, `open scoped BigOperators Topology`, `open NumberField`, `open scoped NumberField nonZeroDivisors`, `open scoped BigOperators ArithmeticFunction.zeta`, `open Finset`, `open scoped BigOperators Classical ArithmeticFunction.Moebius`, `open Finset Nat ArithmeticFunction BoundingSieve`, `open scoped BigOperators Classical`, `open Finset Nat`, `open scoped BigOperators`, `open Filter Topology`, `open scoped nonZeroDivisors`, `open Ideal NumberField Finset UniqueFactorizationMonoid`, `open Filter Set Topology NumberField`, `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors`, `open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace`, `open Filter Set Topology`, `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace`, `open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix`, `open MeasureTheory Filter Set Module TopologicalSpace`, `open MeasureTheory Filter Set`, `open scoped BigOperators Topology ENNReal`, `open scoped BigOperators Topology ENNReal Classical`, `open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise`, `open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise`, `open scoped BigOperators Topology ENNReal Classical Matrix Pointwise`, `open scoped BigOperators Topology ENNReal Classical Matrix`, `open MeasureTheory ProbabilityTheory Filter Set`, `open Set Filter`, `open scoped Topology`, `open scoped Classical`, `open scoped Topology ENNReal Classical`, `open scoped ENNReal Classical`, `open MeasureTheory Set Topology UniformSpace TopologicalSpace`, `open scoped ENNReal Topology`, `open MeasureTheory Filter Set Matrix`, `open scoped Topology Classical`, `open scoped Matrix Classical`, `open scoped Topology Classical Matrix`, `open scoped Classical Pointwise`, `open scoped Topology Classical ENNReal`, `open scoped Matrix Topology Classical`, `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Matrix Topology Classical ENNReal ProbabilityTheory`, `open scoped ENNReal ProbabilityTheory`, `open Set Filter Topology`, `open Set Filter Topology MeasureTheory`, `open MeasureTheory Set Filter Topology`, `open MeasureTheory ProbabilityTheory Set Filter Topology`, `open scoped Matrix ENNReal NNReal ProbabilityTheory`, `open MeasureTheory`, `open scoped BigOperators ENNReal`, `open NumberField Finset`, `open NumberField Filter Set Topology`, `open MeasureTheory ProbabilityTheory Matrix`, `open scoped Classical BigOperators ENNReal`, `open MeasureTheory Set Filter Topology Module`, `open scoped BigOperators SchwartzMap`, `open MeasureTheory Set Filter Topology Module WithLp`, `open scoped BigOperators SchwartzMap ZeroAtInfty`, `open scoped FourierTransform`, `open scoped BigOperators SchwartzMap FourierTransform`, `open scoped BigOperators FourierTransform`, `open MeasureTheory Set Filter Topology Module WithLp Asymptotics`, `open Module WithLp MeasureTheory`, `open scoped BigOperators Matrix`, `open Module MeasureTheory`, `open MeasureTheory Module WithLp`, `open scoped BigOperators NumberField nonZeroDivisors ENNReal`, `open Complex Set Metric Filter`, `open Complex Set Metric Filter MeromorphicOn`, `open scoped Topology ComplexConjugate`, `open MeasureTheory Set Filter`):
--
--   ```lean
--   theorem hasSum_realZeroPole {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
--       (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z)
--       (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
--       HasSum (realZeroPole f σ) (logDeriv f σ).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.AnalyticGrowth.HasSubquadraticGrowth` and `OAI.PrimeDegreePackets.AnalyticGrowth.realZeroPole` (definitions bundle `OAIQ244Duke012` of this split).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.logRegularized_deriv_bound_of_completedXi_gap` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/ZeroReflection.lean (declaration OAI.PrimeDegreePackets.AnalyticGrowth.hasSum_realZeroPole)

import Mathlib
import Definitions.Def_OAIQ244Duke012

section

attribute [-instance] _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter

namespace PrimeDegreePackets.AnalyticGrowth

theorem hasSum_realZeroPole {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    HasSum (realZeroPole f σ) (logDeriv f σ).re := by
  sorry

end PrimeDegreePackets.AnalyticGrowth

end
end

end OAI
end
