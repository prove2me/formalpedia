-- Prove2me | Theorems.Thm_GlobalTheory_SS_exists_semiAbelian_model_of_proper_base
-- name    : GlobalTheory.SS.exists_semiAbelian_model_of_proper_base
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:13.550148+00:00
-- url     : https://prove2.me/theorems/abbe10a0-92bc-492a-9e30-c526c6a5351b
-- title:
--   SS: exists semi Abelian model of proper base
-- statement:
--   The SS construction uses the exists semi Abelian model of proper base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSemiAbelianModelOfProperBase.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSemiAbelianModelOfProperBase.lean#L18-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSemiAbelianModelOfProperBase
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

theorem GlobalTheory.SS.exists_semiAbelian_model_of_proper_base :
    ∀ (o W L : Type) [CommRing o] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (β : o →+* W) (Z : Scheme.{0}) (s : Z ⟶ Sp o) (x : Sp L ⟶ Z) (G : Over Z) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper s → x ≫ s = spMap ((algebraMap W L).comp β) → IsSemiAbelian G → IsGrpPullback A G x φ → ∃ (G' : Over (Sp W)) (_ : GrpObj G') (e : (Over.pullback (spMap (algebraMap W L))).obj G' ≅ A), IsSemiAbelian G' ∧ IsMonHom e.hom := by sorry
