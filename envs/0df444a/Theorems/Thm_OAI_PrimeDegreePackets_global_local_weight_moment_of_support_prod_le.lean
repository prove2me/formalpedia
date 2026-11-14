-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_global_local_weight_moment_of_support_prod_le
-- name    : OAI.PrimeDegreePackets.global_local_weight_moment_of_support_prod_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:40.879215+00:00
-- url     : https://prove2.me/theorems/a7fc493b-62a2-4c90-a057-887f8eb5ba72
-- title:
--   OAI.PrimeDegreePackets.global_local_weight_moment_of_support_prod_le: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.global_local_weight_moment_of_support_prod_le` of [lean/OAI/NumberTheory/PrimePackets/LocalModels.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/LocalModels.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets`, with `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal`, `open MeasureTheory Filter Set Module`, `open scoped TensorProduct`, `open Set Module`, `open MeasureTheory Set`, `open scoped ENNReal`, `open IsDiscreteValuationRing IsLocalRing`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set IsDiscreteValuationRing`, `open Filter`, `open scoped BigOperators Topology`, `open MeasureTheory Set IsDiscreteValuationRing`, `open scoped ENNReal BigOperators`):
--
--   ```lean
--   theorem global_local_weight_moment_of_support_prod_le
--       (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
--       (hL : ∀ p, MeasurableSet (L p : Set (∀ i, R p i)))
--       (hprod : (∏ p ∈ S, (p : ℝ)) ≤ (localIndexProduct S ι R L : ℝ))
--       (hsat : ∀ p, Ideal.span (L p : Set (∀ i, R p i)) = ⊤)
--       (e f : ∀ p, ι p → ℕ) (he0 : ∀ p i, 0 < e p i) (hf0 : ∀ p i, 0 < f p i)
--       (he : ∀ p i, addVal (R p i) (algebraMap (PadicInt p.val) (R p i) p.val) = e p i)
--       (hcard : ∀ p i, Nat.card (IsLocalRing.ResidueField (R p i)) = p.val ^ f p i)
--       (hdegree : ∀ p, ∑ i, f p i * e p i = n) :
--       (∑' k : ∀ p, ι p → ℕ, packetLocalWeight S ι R ν L k *
--         packetLocalNorm S ι R k ^ (1 / (2 * (n : ℝ)) - 1)) ≤
--         (localIndexProduct S ι R L : ℝ≥0∞)⁻¹ *
--           ENNReal.ofReal (localProductConstant n ε hε * (localIndexProduct S ι R L : ℝ) ^ ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.localIndexProduct`, `OAI.PrimeDegreePackets.packetLocalNorm` and `OAI.PrimeDegreePackets.packetLocalWeight` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.localProductConstant` (definitions bundle `OAIQ244Duke024` of this split).
--
--   **Used by.** The proof of `OAI.PrimeDegreePackets.primaryIdeal_reciprocal_tail` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/LocalModels.lean (declaration OAI.PrimeDegreePackets.global_local_weight_moment_of_support_prod_le)

import Mathlib
import Definitions.Def_OAIQ244Duke024

section

attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators

section
variable (n : ℕ) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (ι : S → Type*) [∀ p, Fintype (ι p)]
    (R : ∀ p : S, ι p → Type*)
    [∀ p i, CommRing (R p i)] [∀ p i, IsDomain (R p i)]
    [∀ p i, IsDiscreteValuationRing (R p i)]
    [∀ p i, Algebra (PadicInt p.val) (R p i)]
    [∀ p i, TopologicalSpace (R p i)] [∀ p i, IsTopologicalRing (R p i)]
    [∀ p i, CompactSpace (R p i)] [∀ p i, T2Space (R p i)]
    [∀ p i, MeasurableSpace (R p i)] [∀ p i, BorelSpace (R p i)]
    [∀ p i, SecondCountableTopology (R p i)]
    [∀ p, MeasurableSpace (∀ i, R p i)ˣ] [∀ p, BorelSpace (∀ i, R p i)ˣ]
    (μ : ∀ p i, Measure (R p i)) [∀ p i, IsProbabilityMeasure (μ p i)]
    [∀ p i, (μ p i).IsAddHaarMeasure]
    (ν : ∀ p, Measure (∀ i, R p i)ˣ) [∀ p, IsProbabilityMeasure (ν p)]
    [∀ p, (ν p).IsMulRightInvariant]
    (L : ∀ p : S, Submodule (PadicInt p.val) (∀ i, R p i))
    [∀ p, Finite ((∀ i, R p i) ⧸ L p)]

include μ in

theorem global_local_weight_moment_of_support_prod_le
    (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (hL : ∀ p, MeasurableSet (L p : Set (∀ i, R p i)))
    (hprod : (∏ p ∈ S, (p : ℝ)) ≤ (localIndexProduct S ι R L : ℝ))
    (hsat : ∀ p, Ideal.span (L p : Set (∀ i, R p i)) = ⊤)
    (e f : ∀ p, ι p → ℕ) (he0 : ∀ p i, 0 < e p i) (hf0 : ∀ p i, 0 < f p i)
    (he : ∀ p i, addVal (R p i) (algebraMap (PadicInt p.val) (R p i) p.val) = e p i)
    (hcard : ∀ p i, Nat.card (IsLocalRing.ResidueField (R p i)) = p.val ^ f p i)
    (hdegree : ∀ p, ∑ i, f p i * e p i = n) :
    (∑' k : ∀ p, ι p → ℕ, packetLocalWeight S ι R ν L k *
      packetLocalNorm S ι R k ^ (1 / (2 * (n : ℝ)) - 1)) ≤
      (localIndexProduct S ι R L : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (localProductConstant n ε hε * (localIndexProduct S ι R L : ℝ) ^ ε) := by
  sorry

end

end PrimeDegreePackets

end
end

end OAI
end
