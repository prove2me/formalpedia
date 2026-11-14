-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_weightedIdeal_realInterval_of_zeta_scale
-- name    : OAI.PrimeDegreePackets.weightedIdeal_realInterval_of_zeta_scale
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:00.713228+00:00
-- url     : https://prove2.me/theorems/02a427ba-6d0a-40b4-ad67-9002dc5c1914
-- title:
--   OAI.PrimeDegreePackets.weightedIdeal_realInterval_of_zeta_scale: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.weightedIdeal_realInterval_of_zeta_scale` of [lean/OAI/NumberTheory/PrimePackets/HaarUniqueness.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/HaarUniqueness.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets`, with `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal`, `open MeasureTheory Filter Set Module`, `open scoped TensorProduct`, `open Set Module`, `open MeasureTheory Set`, `open scoped ENNReal`, `open IsDiscreteValuationRing IsLocalRing`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set IsDiscreteValuationRing`, `open Filter`, `open scoped BigOperators Topology`, `open NumberField`, `open scoped NumberField nonZeroDivisors`, `open scoped BigOperators ArithmeticFunction.zeta`, `open Finset`, `open scoped BigOperators Classical`, `open Finset Nat ArithmeticFunction BoundingSieve`, `open scoped BigOperators Classical`, `open Finset Nat`, `open scoped BigOperators`, `open Filter Topology`, `open scoped nonZeroDivisors`, `open Ideal NumberField Finset UniqueFactorizationMonoid`, `open Filter Set Topology NumberField`, `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors`, `open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace`, `open Filter Set Topology`, `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace`, `open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix`, `open MeasureTheory Filter Set Module TopologicalSpace`, `open MeasureTheory Filter Set`, `open scoped BigOperators Topology ENNReal`, `open scoped BigOperators Topology ENNReal Classical`, `open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise`, `open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise`, `open scoped BigOperators Topology ENNReal Classical Matrix Pointwise`, `open scoped BigOperators Topology ENNReal Classical Matrix`, `open MeasureTheory ProbabilityTheory Filter Set`, `open Set Filter`, `open scoped Topology`, `open scoped Classical`, `open scoped Topology ENNReal Classical`, `open scoped ENNReal Classical`, `open MeasureTheory Set Topology UniformSpace TopologicalSpace`, `open scoped ENNReal Topology`):
--
--   ```lean
--   theorem weightedIdeal_realInterval_of_zeta_scale (n : ℕ) (hn0 : 0 < n)
--       {A : ℝ} (hA : 0 < A)
--       (Hscale : ∀ᶠ Q : ℝ in atTop,
--         ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K],
--           (K →+* ℝ) → Module.finrank ℚ K = n →
--           |(NumberField.discr K : ℝ)| ≤ Q^2 →
--           ∀ b : ℝ, Q^(3/4:ℝ) ≤ b →
--             realDedekindZeta K (1+1/Real.log b) / Real.log b ≤
--               A*NumberField.dedekindZeta_residue K) :
--       ∃ C : ℝ, 0 < C ∧ ∀ A₀ : ℝ, 1 ≤ A₀ → ∀ η : ℝ, 0 < η →
--         ∀ᶠ Q : ℝ in atTop,
--         ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
--           (M : FullLattice n K), (K →+* ℝ) →
--           Module.finrank ℚ K = n → |(NumberField.discr K : ℝ)| ≤ Q^2 →
--           (saturationIndex M : ℝ) ≤ Q →
--           ∀ x y : ℝ, Q^(3/4:ℝ) ≤ x → x ≤ A₀*Q → η*x ≤ y → y ≤ x →
--             weightedIdealRealInterval M x y ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
--               ENNReal.ofReal (C*y*NumberField.dedekindZeta_residue K)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.realDedekindZeta` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.saturationIndex` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.weightedIdealRealInterval` (definitions bundle `OAIQ244Duke036` of this split); `OAI.PrimeDegreePackets.FullLattice` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proofs of `OAI.PrimeDegreePackets.packet_limit_ball_bound_of_zeta_scale` and `OAI.PrimeDegreePackets.packet_tight_of_zeta_scale` of this split import it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/HaarUniqueness.lean (declaration OAI.PrimeDegreePackets.weightedIdeal_realInterval_of_zeta_scale)

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open scoped BigOperators Classical
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

namespace PrimeDegreePackets

theorem weightedIdeal_realInterval_of_zeta_scale (n : ℕ) (hn0 : 0 < n)
    {A : ℝ} (hA : 0 < A)
    (Hscale : ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K],
        (K →+* ℝ) → Module.finrank ℚ K = n →
        |(NumberField.discr K : ℝ)| ≤ Q^2 →
        ∀ b : ℝ, Q^(3/4:ℝ) ≤ b →
          realDedekindZeta K (1+1/Real.log b) / Real.log b ≤
            A*NumberField.dedekindZeta_residue K) :
    ∃ C : ℝ, 0 < C ∧ ∀ A₀ : ℝ, 1 ≤ A₀ → ∀ η : ℝ, 0 < η →
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice n K), (K →+* ℝ) →
        Module.finrank ℚ K = n → |(NumberField.discr K : ℝ)| ≤ Q^2 →
        (saturationIndex M : ℝ) ≤ Q →
        ∀ x y : ℝ, Q^(3/4:ℝ) ≤ x → x ≤ A₀*Q → η*x ≤ y → y ≤ x →
          weightedIdealRealInterval M x y ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C*y*NumberField.dedekindZeta_residue K) := by
  sorry

open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators

end PrimeDegreePackets
end
end

end OAI
end
