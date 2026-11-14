-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_fixedFieldMultiplicity_le_extension
-- name    : OAI.DukePrimeDegree.fixedFieldMultiplicity_le_extension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:39:11.227313+00:00
-- url     : https://prove2.me/theorems/f7a81334-2836-4114-b9f7-0f975334cdae
-- title:
--   OAI.DukePrimeDegree.fixedFieldMultiplicity_le_extension: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.fixedFieldMultiplicity_le_extension` of [lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/CyclicFixedOrders.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/CyclicFixedOrders.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open scoped NumberField Classical`, `open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter`):
--
--   ```lean
--   theorem fixedFieldMultiplicity_le_extension
--       {N : ℕ} [NeZero N]
--       (ψ : ((E ≃ₐ[IntermediateField.fixedField C] E) →* ℂˣ) →
--         EvenRayCharacter (IntermediateField.fixedField C) N)
--       (hid : ∀ χ, (ψ χ).idealHom = idealHom (IntermediateField.fixedField C) E χ)
--       (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
--       (hD : (NumberField.discr E).natAbs ∣ N)
--       {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
--       fixedFieldMultiplicity β C ≤ zetaMultiplicity E β
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.EvenRayCharacter` and `OAI.PrimeDegreePackets.GaloisIdealCharacter.idealHom` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.EvenRayCharacter.IsNonprincipal` (definitions bundle `OAIQ244Duke022` of this split); `OAI.DukePrimeDegree.fixedFieldMultiplicity` and `OAI.DukePrimeDegree.zetaMultiplicity` (definitions bundle `OAIQ244Duke023` of this split).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.extension_multiplicity_pos_of_ray_realizations` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/CyclicFixedOrders.lean (declaration OAI.DukePrimeDegree.fixedFieldMultiplicity_le_extension)

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
import Definitions.Def_OAIQ244Duke023

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteNormalClosure_numberField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NumberField Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
variable [NumberField.IsTotallyReal E]
variable (C : Subgroup (E ≃ₐ[ℚ] E)) [IsCyclic C]

theorem fixedFieldMultiplicity_le_extension
    {N : ℕ} [NeZero N]
    (ψ : ((E ≃ₐ[IntermediateField.fixedField C] E) →* ℂˣ) →
      EvenRayCharacter (IntermediateField.fixedField C) N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom (IntermediateField.fixedField C) E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (hD : (NumberField.discr E).natAbs ∣ N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    fixedFieldMultiplicity β C ≤ zetaMultiplicity E β := by
  sorry

end DukePrimeDegree

end

end OAI
end
