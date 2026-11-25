-- Prove2me | Theorems.Thm_GlobalTheory_SharpFamRel_ext_of_dense
-- name    : GlobalTheory.SharpFamRel.ext_of_dense
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:18.279992+00:00
-- url     : https://prove2.me/theorems/acd643ac-2f53-5b9b-80e5-7f1ca305d626
-- title:
--   Sharp Fam Rel: ext of dense
-- statement:
--   The Sharp Fam Rel construction uses the ext of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/E8SharpFamilyMatrixRelationsDense.lean#L85-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/E8SharpFamilyMatrixRelationsDense.lean#L85-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpFamRel

theorem GlobalTheory.SharpFamRel.ext_of_dense {S : Scheme.{0}} {T G : Over S} [IsReduced T.left] (hT : IsOpenMap T.hom) [IsSeparated G.hom]
    (f g : T ⟶ G) {D : Set S} (hD : Dense D)
    (H : ∀ p ∈ D, ∃ (Z Y : Scheme.{0}) (ψ : Z ⟶ T.left) (q : Z ⟶ Y) (x : Y ⟶ S), IsPullback ψ q T.hom x ∧
      p ∈ Set.range x ∧ ψ ≫ f.left = ψ ≫ g.left) : f = g := by sorry
