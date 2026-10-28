-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_source_aligned_disjoint_eventually
-- name    : OAI.SimpleAmenable.source_aligned_disjoint_eventually
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:25:38.918071+00:00
-- url     : https://prove2.me/theorems/e92572bf-e9ea-403a-818a-a32efb585a7b
-- title:
--   OAI.SimpleAmenable.source_aligned_disjoint_eventually: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.source_aligned_disjoint_eventually` of [lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/AlignedGroups.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/AlignedGroups.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem source_aligned_disjoint_eventually (a : ℕ) (r : CutRing) (m : ℕ)
--       (hm : 2 ≤ m) (hm' : 10 < m+1) :
--       ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
--         ∃ t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
--             BoundedRelationCover M (alternatingGenerator a r m hm),
--           (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) = PresentedGroup.of (Sum.inr i)) ∧
--           (coverMap M (alternatingGenerator a r m hm)).comp t = sourceLatticeMap a r m hm ∧
--           ∀ (I J : Finset (Fin (m+1))), Disjoint I J →
--             ∀ g ∈ sourceAlignedGroup a r m hm M t I,
--             ∀ h ∈ sourceAlignedGroup a r m hm M t J, Commute g h
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.coverMap`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup`, `OAI.SimpleAmenable.shortRelations` and `OAI.SimpleAmenable.sourceLatticeMap` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.sourceAlignedGroup` (definitions bundle `OAIQ65Sa005` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.initialCoverSystem_eventually` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/AlignedGroups.lean (declaration OAI.SimpleAmenable.source_aligned_disjoint_eventually)

import Mathlib
import Definitions.Def_OAIQ65Sa005

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

section SourceAlignedGroups

theorem source_aligned_disjoint_eventually (a : ℕ) (r : CutRing) (m : ℕ)
    (hm : 2 ≤ m) (hm' : 10 < m+1) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
        (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) = PresentedGroup.of (Sum.inr i)) ∧
        (coverMap M (alternatingGenerator a r m hm)).comp t = sourceLatticeMap a r m hm ∧
        ∀ (I J : Finset (Fin (m+1))), Disjoint I J →
          ∀ g ∈ sourceAlignedGroup a r m hm M t I,
          ∀ h ∈ sourceAlignedGroup a r m hm M t J, Commute g h := by
  sorry

end SourceAlignedGroups

end SimpleAmenable
end
end

end OAI
end
