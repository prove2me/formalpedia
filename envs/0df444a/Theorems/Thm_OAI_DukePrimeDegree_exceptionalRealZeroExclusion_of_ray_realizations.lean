-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exceptionalRealZeroExclusion_of_ray_realizations
-- name    : OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:37:11.898218+00:00
-- url     : https://prove2.me/theorems/0adbba50-cd04-4939-94a2-efbd733ddae8
-- title:
--   OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations` of [lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/StarkNormalClosure.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/StarkNormalClosure.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Module Set IntermediateField`, `open scoped NumberField Classical`, `open PrimeDegreePackets PrimeDegreePackets.HeckeMellin PrimeDegreePackets.AnalyticGrowth`):
--
--   ```lean
--   theorem exceptionalRealZeroExclusion_of_ray_realizations
--       (d : ℕ) (hodd : Odd (d + 1))
--       (hray : ∀ (E : Type u) [Field E] [NumberField E] [IsGalois ℚ E]
--         [NumberField.IsTotallyReal E], HasCyclicRayRealizations E) :
--       ExceptionalRealZeroExclusion.{u} d
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.ExceptionalRealZeroExclusion` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.HasCyclicRayRealizations` (definitions bundle `OAIQ244Duke022` of this split).
--
--   **Used by.** The proofs of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional` of this split import it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/StarkNormalClosure.lean (declaration OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations)

import Mathlib
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_OAIQ244Duke022

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module Set IntermediateField
open scoped NumberField Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.HeckeMellin PrimeDegreePackets.AnalyticGrowth

universe u

theorem exceptionalRealZeroExclusion_of_ray_realizations
    (d : ℕ) (hodd : Odd (d + 1))
    (hray : ∀ (E : Type u) [Field E] [NumberField E] [IsGalois ℚ E]
      [NumberField.IsTotallyReal E], HasCyclicRayRealizations E) :
    ExceptionalRealZeroExclusion.{u} d := by
  sorry

end DukePrimeDegree

end

end OAI
end
