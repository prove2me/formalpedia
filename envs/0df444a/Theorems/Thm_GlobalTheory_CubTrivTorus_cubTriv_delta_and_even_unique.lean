-- Prove2me | Theorems.Thm_GlobalTheory_CubTrivTorus_cubTriv_delta_and_even_unique
-- name    : GlobalTheory.CubTrivTorus.cubTriv_delta_and_even_unique
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:15:57.606337+00:00
-- url     : https://prove2.me/theorems/5b9f29f5-5d9b-4e89-8a26-5f936bad1d23
-- title:
--   Cub Triv Torus: cub Triv delta and even unique
-- statement:
--   The Cub Triv Torus construction uses the cub Triv delta and even unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubTrivDeltaAndEvenUnique.lean#L318-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubTrivDeltaAndEvenUnique.lean#L318-L320

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubTrivTorus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable [ConnectedSpace S] [Module.Free ℤ X] {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G}
  [IsMonHom i]

theorem GlobalTheory.CubTrivTorus.cubTriv_delta_and_even_unique : (∀ (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G] (P : CP G) (i : splitTorus S X ⟶ G), IsMonHom i → (∀ (s : BiTriv P.c i) (σ : CubTriv P.c i) (T : Over S) (t t' : T ⟶ splitTorus S X) (z : T.left) (J), Good P.L.L z J → val σ.s (t * t').left z J = val s.s (lift t (t' ≫ i)).left z J * val σ.s t.left z J * val σ.s t'.left z J) ∧ ∀ σ σ' : CubTriv P.c i, σ.Even → σ'.Even → σ = σ') := by sorry
