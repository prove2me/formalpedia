-- Prove2me | Theorems.Thm_GlobalTheory_SS_isSemiAbelian_of_proper_generic_of_torusExtension
-- name    : GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:10:04.577821+00:00
-- url     : https://prove2.me/theorems/af125093-6e31-459f-8662-474cbb21a7dd
-- title:
--   SS: is Semi Abelian of proper generic of torus Extension
-- statement:
--   The SS construction uses the is Semi Abelian of proper generic of torus Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber.lean#L77-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber.lean#L77-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
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

theorem GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ (k : Type) [Field k] (ρ : W →+* k), RingHom.ker ρ = IsLocalRing.maximalIdeal W → ρ.IsIntegral → Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj G)) → IsSemiAbelian G := by sorry
