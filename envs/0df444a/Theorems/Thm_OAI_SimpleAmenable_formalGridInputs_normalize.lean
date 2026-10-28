-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_formalGridInputs_normalize
-- name    : OAI.SimpleAmenable.formalGridInputs_normalize
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:25:40.351566+00:00
-- url     : https://prove2.me/theorems/09bff38f-253f-4376-9750-29c510846497
-- title:
--   OAI.SimpleAmenable.formalGridInputs_normalize: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.formalGridInputs_normalize` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FormalGridPieces.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FormalGridPieces.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem formalGridInputs_normalize [∀ i, Finite (κ i)]
--       (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
--       (h20 : 20 ≤ Fintype.card α)
--       (hconj : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
--       (hdis : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
--       (hF : ∀ i j, SmallSupported L (F i j))
--       (hc : ∀ i, F i none=c.comp (universalProjection _))
--       (j k : D → TrackStar α →* H)
--       (hj : ∀ i d, (T i).sector (C i d)=j d)
--       (hk : ∀ i d, (T i).sector (C i d)ᶜ=k d)
--       (hjs : ∀ d, SmallSupported L (j d))
--       (hcomm : ∀ d s t, Commute (j d s) (k d t)) :
--       ∀ d i s, formalGridInput F T U i s ∈
--         Subgroup.normalizer ((⨆ i, (formalGridPiece F T U C d i).range : Subgroup H) : Set H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.UniversalExtension`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations` and `OAI.SimpleAmenable.universalProjection` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.TrackStar` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.FormalStarTable`, `OAI.SimpleAmenable.SmallSupported` and `OAI.SimpleAmenable.FormalStarTable.sector` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.formalGridInput` and `OAI.SimpleAmenable.formalGridPiece` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.independent_actual_patching` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FormalGridPieces.lean (declaration OAI.SimpleAmenable.formalGridInputs_normalize)

import Mathlib
import Definitions.Def_OAIQ65Sa014

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
section FormalGridPieces
variable {α H ι D : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)] {κ : ι → Type*}
    (F : (i : ι) → Option (κ i) → TrackStar α →* H)
    (T : ∀ i, FormalStarTable (F i)) (U : (i : ι) → Set (κ i → Bool))
    (C : (i : ι) → D → Set (κ i → Bool))

theorem formalGridInputs_normalize [∀ i, Finite (κ i)]
    (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
    (h20 : 20 ≤ Fintype.card α)
    (hconj : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hdis : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (hF : ∀ i j, SmallSupported L (F i j))
    (hc : ∀ i, F i none=c.comp (universalProjection _))
    (j k : D → TrackStar α →* H)
    (hj : ∀ i d, (T i).sector (C i d)=j d)
    (hk : ∀ i d, (T i).sector (C i d)ᶜ=k d)
    (hjs : ∀ d, SmallSupported L (j d))
    (hcomm : ∀ d s t, Commute (j d s) (k d t)) :
    ∀ d i s, formalGridInput F T U i s ∈
      Subgroup.normalizer ((⨆ i, (formalGridPiece F T U C d i).range : Subgroup H) : Set H) := by
  sorry

end FormalGridPieces

end SimpleAmenable
end
end

end OAI
end
