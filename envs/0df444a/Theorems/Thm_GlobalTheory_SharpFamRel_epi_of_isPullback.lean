-- Prove2me | Theorems.Thm_GlobalTheory_SharpFamRel_epi_of_isPullback
-- name    : GlobalTheory.SharpFamRel.epi_of_isPullback
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:49:51.811476+00:00
-- url     : https://prove2.me/theorems/7602f33b-c17c-496a-b259-2f88cfa66dd5
-- title:
--   Sharp Fam Rel: epi of is Pullback
-- statement:
--   The Sharp Fam Rel construction uses the epi of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/E8SharpFamilyMatrixRelationsDense.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/E8SharpFamilyMatrixRelationsDense.lean#L20-L27

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

theorem GlobalTheory.SharpFamRel.epi_of_isPullback {K : Type} [Field K] {S' : Scheme.{0}} {f : S' ⟶ Sp K} [Nonempty S'] {X₀ X : Scheme.{0}}
    {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀} (H : IsPullback h p p₀ f) : Epi h := by sorry
