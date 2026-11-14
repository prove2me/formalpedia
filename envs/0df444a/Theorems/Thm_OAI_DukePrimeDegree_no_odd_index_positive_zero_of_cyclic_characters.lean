-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_no_odd_index_positive_zero_of_cyclic_characters
-- name    : OAI.DukePrimeDegree.no_odd_index_positive_zero_of_cyclic_characters
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:44:46.536709+00:00
-- url     : https://prove2.me/theorems/ad85452f-dbdd-4592-9f39-4f9bfe2fe459
-- title:
--   OAI.DukePrimeDegree.no_odd_index_positive_zero_of_cyclic_characters: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.no_odd_index_positive_zero_of_cyclic_characters` of [lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/StarkDescent.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/StarkDescent.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open scoped NumberField BigOperators Classical`, `open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter`):
--
--   ```lean
--   theorem no_odd_index_positive_zero_of_cyclic_characters
--       {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
--       (hcyclic : ∀ C : Subgroup (E ≃ₐ[ℚ] E), IsCyclic C → ∃ χ : C →* ℝˣ,
--         (∀ x : C, fixedFieldMultiplicity β (Subgroup.zpowers (x : E ≃ₐ[ℚ] E)) =
--           if χ x = 1 then 1 else 0) ∧
--         fixedFieldMultiplicity β C = if χ = 1 then 1 else 0)
--       (H : Subgroup (E ≃ₐ[ℚ] E)) (hodd : Odd H.index)
--       (hH : 0 < fixedFieldMultiplicity β H) (hQ : zetaMultiplicity ℚ β = 0) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.starkDescentFintype` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.fixedFieldMultiplicity` and `OAI.DukePrimeDegree.zetaMultiplicity` (definitions bundle `OAIQ244Duke023` of this split).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/StarkDescent.lean (declaration OAI.DukePrimeDegree.no_odd_index_positive_zero_of_cyclic_characters)

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
import Definitions.Def_OAIQ244Duke023

section

attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
variable [NumberField.IsTotallyReal E]

attribute [local instance] OAI.DukePrimeDegree.starkDescentFintype
theorem no_odd_index_positive_zero_of_cyclic_characters
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcyclic : ∀ C : Subgroup (E ≃ₐ[ℚ] E), IsCyclic C → ∃ χ : C →* ℝˣ,
      (∀ x : C, fixedFieldMultiplicity β (Subgroup.zpowers (x : E ≃ₐ[ℚ] E)) =
        if χ x = 1 then 1 else 0) ∧
      fixedFieldMultiplicity β C = if χ = 1 then 1 else 0)
    (H : Subgroup (E ≃ₐ[ℚ] E)) (hodd : Odd H.index)
    (hH : 0 < fixedFieldMultiplicity β H) (hQ : zetaMultiplicity ℚ β = 0) : False := by
  sorry

end DukePrimeDegree

end

end OAI
end
