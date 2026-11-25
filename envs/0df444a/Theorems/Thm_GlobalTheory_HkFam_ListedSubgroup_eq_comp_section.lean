-- Prove2me | Theorems.Thm_GlobalTheory_HkFam_ListedSubgroup_eq_comp_section
-- name    : GlobalTheory.HkFam.ListedSubgroup.eq_comp_section
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:37:04.257169+00:00
-- url     : https://prove2.me/theorems/be3efd79-bb0b-45de-ab20-5d4b33837553
-- title:
--   Listed Subgroup: eq comp section
-- statement:
--   The Listed Subgroup construction uses the eq comp section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupEqRangeOfLists.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupEqRangeOfLists.lean#L18-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_KerScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupEqRangeOfLists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
open GlobalTheory GlobalTheory.HkFam GlobalTheory.HkFam.ListedSubgroup
variable {S : Scheme.{0}}

theorem GlobalTheory.HkFam.ListedSubgroup.eq_comp_section {X : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    {k : Type} [Field k] (z : Sp k ⟶ X) (q : Sp k) (hz : z q ∈ Set.range s) : z = (z ≫ f) ≫ s := by sorry
