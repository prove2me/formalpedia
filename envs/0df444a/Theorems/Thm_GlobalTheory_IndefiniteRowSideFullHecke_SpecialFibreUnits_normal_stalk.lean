-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SpecialFibreUnits_normal_stalk
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.normal_stalk
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:32.449747+00:00
-- url     : https://prove2.me/theorems/4b174784-68f0-4194-9a9d-cab57e6f1994
-- title:
--   Special Fibre Units: normal stalk
-- statement:
--   The Special Fibre Units construction uses the normal stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/SpecialFibreUnits.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/SpecialFibreUnits.lean#L120-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

theorem GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.normal_stalk (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (z : PrimeSpectrum A) : IsIntegrallyClosed ((Spec.structureSheaf A).presheaf.stalk z) := by sorry
