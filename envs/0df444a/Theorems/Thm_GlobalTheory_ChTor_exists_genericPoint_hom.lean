-- Prove2me | Theorems.Thm_GlobalTheory_ChTor_exists_genericPoint_hom
-- name    : GlobalTheory.ChTor.exists_genericPoint_hom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T18:02:05.010505+00:00
-- url     : https://prove2.me/theorems/a69f75f7-0374-50d2-a564-04f04bedf92c
-- title:
--   Ch Tor: exists generic Point hom
-- statement:
--   The Ch Tor construction uses the exists generic Point hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsGenericPointHom.lean#L17-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsGenericPointHom.lean#L17-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ChartPoints_ChartPt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsGenericPointHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChTor
open GlobalTheory GlobalTheory.ChTor

theorem GlobalTheory.ChTor.exists_genericPoint_hom (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C)) (G : Over (Sp O)) [GrpObj G] (hsep : IsSeparated G.hom)
    (A : Over (Sp C)) [GrpObj A] (gen : A.left ⟶ G.left)
    (h : IsGrpPullback A G (spMap (algebraMap O C)) gen) :
    ∃ j : (algOver O O ⟶ G) →* Pts A, Function.Injective j ∧
      ∀ P z, z.left ≫ gen = spMap (algebraMap O C) ≫ P.left ↔ z = j P := by sorry
