-- Prove2me | Theorems.Thm_GlobalTheory_SS_GlueCompat_ofSquare_j
-- name    : GlobalTheory.SS.GlueCompat.ofSquare_j
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:58:02.737472+00:00
-- url     : https://prove2.me/theorems/23bce90a-ece6-471f-9de6-8f69b384a6b2
-- title:
--   Glue Compat: of Square j
-- statement:
--   The Glue Compat construction uses the of Square j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGlueFinitelyManyCompatibleSmoothModels.lean#L176-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGlueFinitelyManyCompatibleSmoothModels.lean#L176-L178

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GlueCompat
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem GlobalTheory.SS.GlueCompat.ofSquare_j (Y : Over (Sp R)) (h₁ : Smooth Y.hom) (h₂ : IsSeparated Y.hom) (h₃ : QuasiCompact Y.hom)
    {j : A.left ⟶ Y.left} (h : IsPullback j A.hom Y.hom (spMap (algebraMap R K))) :
    (ofSquare Y h₁ h₂ h₃ h).j = j := by sorry
