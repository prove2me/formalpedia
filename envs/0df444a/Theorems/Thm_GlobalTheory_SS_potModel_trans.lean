-- Prove2me | Theorems.Thm_GlobalTheory_SS_potModel_trans
-- name    : GlobalTheory.SS.potModel_trans
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:38:04.136258+00:00
-- url     : https://prove2.me/theorems/95c7d708-f333-4a82-b4b9-f9990291fe61
-- title:
--   SS: pot Model trans
-- statement:
--   The SS construction uses the pot Model trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PotModelTrans.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PotModelTrans.lean#L19-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PotModelTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open GlobalTheory GlobalTheory.SS
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

theorem GlobalTheory.SS.potModel_trans : ∀ (V K V₁ K₁ : Type) [CommRing V] [Field K] [Algebra V K] [CommRing V₁] [Field K₁] [Algebra V₁ K₁] [Algebra V V₁] [Algebra K K₁], (algebraMap V₁ K₁).comp (algebraMap V V₁) = (algebraMap K K₁).comp (algebraMap V K) → Module.Finite V V₁ → IsLocalHom (algebraMap V V₁) → ∀ (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (A₁ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K₁)) [GrpObj A₁] (φ : A₁.left ⟶ A.left), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A₁ A (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K₁)) φ → ∀ Q, _root_.GlobalTheory.SS.PotModel V₁ K₁ A₁ Q → _root_.GlobalTheory.SS.PotModel V K A Q := by sorry
