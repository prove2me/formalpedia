-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_growth_axis_law_of_anchor
-- name    : OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law_of_anchor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:36:26.806978+00:00
-- url     : https://prove2.me/theorems/c3f5b5d3-9978-4593-b18a-9fc40e4ccc0d
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law_of_anchor: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law_of_anchor` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/GrowthGeneration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/GrowthGeneration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem growth_axis_law_of_anchor (hlarge : 15 < m+1) (n : ℕ) (hn : 1005 ≤ n)
--       (g : B.CoordinateWindowLaw n) (d : Fin 2) (p : ℤ)
--       (h : CentralOn (coverMap M (alternatingGenerator a r m hm))
--         ((growthAnchorFamily n hn p).prefixGroup B hlarge g d))
--       (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) :
--       B.PrimitiveFamilyLaw I b hb (axisWindowPrimitives d (growthNewLength n) p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralOn`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.coverMap`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup` and `OAI.SimpleAmenable.shortRelations` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.growthAnchorLength`, `OAI.SimpleAmenable.growthAnchorStart` and `OAI.SimpleAmenable.growthNewLength` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.axisWindowPrimitives`, `OAI.SimpleAmenable.AxisAnchorFamily.prefixGroup`, `OAI.SimpleAmenable.InitialCoverSystem.CoordinateWindowLaw` and `OAI.SimpleAmenable.InitialCoverSystem.PrimitiveFamilyLaw` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.growthAnchorFamily` (definitions bundle `OAIQ65Sa009` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/GrowthGeneration.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law_of_anchor)

import Mathlib
import Definitions.Def_OAIQ65Sa009

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section GrowthAxisLaw
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem growth_axis_law_of_anchor (hlarge : 15 < m+1) (n : ℕ) (hn : 1005 ≤ n)
    (g : B.CoordinateWindowLaw n) (d : Fin 2) (p : ℤ)
    (h : CentralOn (coverMap M (alternatingGenerator a r m hm))
      ((growthAnchorFamily n hn p).prefixGroup B hlarge g d))
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) :
    B.PrimitiveFamilyLaw I b hb (axisWindowPrimitives d (growthNewLength n) p) := by
  sorry

end InitialCoverSystem
end GrowthAxisLaw

end SimpleAmenable
end
end

end OAI
end
