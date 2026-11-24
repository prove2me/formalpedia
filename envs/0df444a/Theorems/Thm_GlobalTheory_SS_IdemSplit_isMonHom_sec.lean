-- Prove2me | Theorems.Thm_GlobalTheory_SS_IdemSplit_isMonHom_sec
-- name    : GlobalTheory.SS.IdemSplit.isMonHom_sec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:35:11.454826+00:00
-- url     : https://prove2.me/theorems/b2eac5ff-38dc-451c-9ff5-4bc93738cf2c
-- title:
--   Idem Split: is Mon Hom sec
-- statement:
--   The Idem Split construction uses the is Mon Hom sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SmConnIdempotentSplits.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SmConnIdempotentSplits.lean#L72-L75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmConnIdempotentSplits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.IdemSplit
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : C} [GrpObj G]
  (i : H ⟶ G) (r : G ⟶ H) (hir : i ≫ r = 𝟙 H) [he : IsMonHom (r ≫ i)]

theorem GlobalTheory.SS.IdemSplit.isMonHom_sec : letI := grpObj i r hir; IsMonHom i := by sorry
