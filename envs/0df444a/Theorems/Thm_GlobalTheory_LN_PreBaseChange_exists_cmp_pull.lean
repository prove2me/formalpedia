-- Prove2me | Theorems.Thm_GlobalTheory_LN_PreBaseChange_exists_cmp_pull
-- name    : GlobalTheory.LN.PreBaseChange.exists_cmp_pull
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:43:17.940187+00:00
-- url     : https://prove2.me/theorems/751269f2-d673-5314-aa87-f825055e764d
-- title:
--   Pre Base Change: exists cmp pull
-- statement:
--   The Pre Base Change construction uses the exists cmp pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCmpOfIsPullDeg.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCmpOfIsPullDeg.lean#L86-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGrpPullbackThick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GtCoordCompatOfPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFourthSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsPreUSetPsi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPsiGeneratingOnWholeSpectrumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsCubicalBundleMapOfPulledBackDegenerationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourthSideRespectsRigSymmetryCubeStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCmpOfIsPullDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.LN GlobalTheory.LN.PreBaseChange

theorem GlobalTheory.LN.PreBaseChange.exists_cmp_pull : Laws → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ (D₁ : DegPre V) (U₁ : PreU I' D₁ A' G') (C : Cmp φ U U₁ F), U₁.P = U'.P ∧ HEq C.wL wL := by sorry
