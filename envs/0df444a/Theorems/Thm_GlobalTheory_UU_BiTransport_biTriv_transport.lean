-- Prove2me | Theorems.Thm_GlobalTheory_UU_BiTransport_biTriv_transport
-- name    : GlobalTheory.UU.BiTransport.biTriv_transport
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T16:45:52.410215+00:00
-- url     : https://prove2.me/theorems/983c0940-964d-44cb-9f2f-7257c458ddf3
-- title:
--   Bi Transport: bi Triv transport
-- statement:
--   The Bi Transport construction uses the bi Triv transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BiTrivTransport.lean#L193-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BiTrivTransport.lean#L193-L195

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BiTrivTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiTransport
variable {S S₀ : Scheme.{0}} {ρ : S₀ ⟶ S}

theorem GlobalTheory.UU.BiTransport.biTriv_transport : ∀ (S S₀ : Scheme.{0}) (ρ : S₀ ⟶ S) [Mono ρ] (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G ρ F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P ρ F hw w → ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat ρ F i₀ i → BiTriv P₀.c i₀ → ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (splitTorus S X ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧ (∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (x : Z ⟶ G) (a b d : Z.left ⟶ pullback (splitTorus S X ⊗ G).hom ρ), a ≫ pullback.fst _ _ = (lift (t * t') x).left → b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t' x).left → ∀ (z : Z.left) (I), Good P.L.L z I → val s a z I = cubV P.c z I (t ≫ i) (t' ≫ i) x * val s b z I * val s d z I) ∧ (∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (x x' : Z ⟶ G) (a b d : Z.left ⟶ pullback (splitTorus S X ⊗ G).hom ρ), a ≫ pullback.fst _ _ = (lift t (x * x')).left → b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t x').left → ∀ (z : Z.left) (I), Good P.L.L z I → val s a z I = cubV P.c z I (t ≫ i) x x' * val s b z I * val s d z I) := by sorry
