-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_formal_pairs_assemble
-- name    : OAI.SimpleAmenable.formal_pairs_assemble
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:48:53.205986+00:00
-- url     : https://prove2.me/theorems/05414e70-e6c2-438b-984d-d8058a6daaf1
-- title:
--   OAI.SimpleAmenable.formal_pairs_assemble: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.formal_pairs_assemble` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FormalPairSplits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FormalPairSplits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem formal_pairs_assemble (hα : 20 ≤ Fintype.card α)
--       (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
--       (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
--       (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
--       (F : Option ι → TrackStar α →* H) (hF : ∀ j, SmallSupported L (F j))
--       (h0 : F none=c.comp (universalProjection (alternatingGroup α)))
--       (T : ∀ i j, FormalStarTable (starPair F i j)) : Nonempty (FormalStarTable F)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.UniversalExtension`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations` and `OAI.SimpleAmenable.universalProjection` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.TrackStar` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.starPair` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.FormalStarTable` and `OAI.SimpleAmenable.SmallSupported` (definitions bundle `OAIQ65Sa011` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.primitive_laws_eventually` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FormalPairSplits.lean (declaration OAI.SimpleAmenable.formal_pairs_assemble)

import Mathlib
import Definitions.Def_OAIQ65Sa009
import Definitions.Def_OAIQ65Sa011

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FormalPairAssembly
variable {α ι H : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem formal_pairs_assemble (hα : 20 ≤ Fintype.card α)
    (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (F : Option ι → TrackStar α →* H) (hF : ∀ j, SmallSupported L (F j))
    (h0 : F none=c.comp (universalProjection (alternatingGroup α)))
    (T : ∀ i j, FormalStarTable (starPair F i j)) : Nonempty (FormalStarTable F) := by
  sorry

end FormalPairAssembly

end SimpleAmenable
end
end

end OAI
end
