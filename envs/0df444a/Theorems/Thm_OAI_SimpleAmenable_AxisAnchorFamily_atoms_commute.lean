-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_AxisAnchorFamily_atoms_commute
-- name    : OAI.SimpleAmenable.AxisAnchorFamily.atoms_commute
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:22:58.722952+00:00
-- url     : https://prove2.me/theorems/f0b29c4c-3e4d-4a42-84a6-651b601f6c35
-- title:
--   OAI.SimpleAmenable.AxisAnchorFamily.atoms_commute: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.AxisAnchorFamily.atoms_commute` of [lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/AxisAnchorFamily.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/AxisAnchorFamily.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.AxisAnchorFamily`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem atoms_commute (h20 : 20 ≤ m+1) :
--       Pairwise fun i j : (Σ i : Fin l, Fin (A.count i)) => ∀ x y,
--         Commute ((A.cuts i.1).atomCopy B hlarge g d (A.intervalLength hl i.1) (hc i.1) i.2 x)
--           ((A.cuts j.1).atomCopy B hlarge g d (A.intervalLength hl j.1) (hc j.1) j.2 y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup` and `OAI.SimpleAmenable.shortRelations` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.AxisAnchorFamily`, `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.AxisAnchorFamily.intervalLength`, `OAI.SimpleAmenable.AxisCutSequence.atomCopy`, `OAI.SimpleAmenable.AxisCutSequence.prefixCopy`, `OAI.SimpleAmenable.AxisCutSequence.suffix` and `OAI.SimpleAmenable.InitialCoverSystem.CoordinateWindowLaw` (definitions bundle `OAIQ65Sa005` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/AxisAnchorFamily.lean (declaration OAI.SimpleAmenable.AxisAnchorFamily.atoms_commute)

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
section AxisAnchorFamily

namespace AxisAnchorFamily
variable {n l : ℕ} {q : ℤ} (A : AxisAnchorFamily n l q)

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (hl : 201 ≤ l) (hln : l ≤ n)

variable (hc : ∀ (i : Fin l) (j k : ℕ), j ≤ k → ∀ x y,
  Commute ((A.cuts i).prefixCopy B hlarge g d j x) ((A.cuts i).suffix B hlarge g d k y))

include hl hln in
theorem atoms_commute (h20 : 20 ≤ m+1) :
    Pairwise fun i j : (Σ i : Fin l, Fin (A.count i)) => ∀ x y,
      Commute ((A.cuts i.1).atomCopy B hlarge g d (A.intervalLength hl i.1) (hc i.1) i.2 x)
        ((A.cuts j.1).atomCopy B hlarge g d (A.intervalLength hl j.1) (hc j.1) j.2 y) := by
  sorry

end AxisAnchorFamily
end AxisAnchorFamily

end SimpleAmenable
end
end

end OAI
end
