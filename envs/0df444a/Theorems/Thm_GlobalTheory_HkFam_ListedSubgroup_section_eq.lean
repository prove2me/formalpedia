-- Prove2me | Theorems.Thm_GlobalTheory_HkFam_ListedSubgroup_section_eq
-- name    : GlobalTheory.HkFam.ListedSubgroup.section_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:37:19.12994+00:00
-- url     : https://prove2.me/theorems/173c76d5-ac54-4c52-8fd4-f9308a1e392b
-- title:
--   Listed Subgroup: section eq
-- statement:
--   The Listed Subgroup construction uses the section eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupEqRangeOfLists.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupEqRangeOfLists.lean#L32-L48

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

theorem GlobalTheory.HkFam.ListedSubgroup.section_eq [ConnectedSpace S] (G : Over S) [GrpObj G] [IsAbelianScheme G] {N : ℕ}
    (hN : IsUnit (N : Γ(S, ⊤))) {a b : 𝟙_ (Over S) ⟶ G} (ha : a ^ N = 1) (hb : b ^ N = 1)
    {k : Type} [Field k] (x : Sp k ⟶ S) (h : x ≫ a.left = x ≫ b.left) : a = b := by sorry
