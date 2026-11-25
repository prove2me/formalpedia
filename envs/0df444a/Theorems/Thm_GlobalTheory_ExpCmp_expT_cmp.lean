-- Prove2me | Theorems.Thm_GlobalTheory_ExpCmp_expT_cmp
-- name    : GlobalTheory.ExpCmp.expT_cmp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:29:04.863534+00:00
-- url     : https://prove2.me/theorems/36c0fc32-b53b-458e-ae81-60560bfe4275
-- title:
--   Exp Cmp: exp T cmp
-- statement:
--   The Exp Cmp construction uses the exp T cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitMapSnd.lean#L96-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnitMapSnd.lean#L96-L175

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MatchingSectionsExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitMapSnd
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
open GlobalTheory GlobalTheory.ExpCmp
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans GlobalTheory.UnitSec
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
set_option maxHeartbeats 1600000

theorem GlobalTheory.ExpCmp.expT_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → ∃ (σ' : U'.SecGT (𝟙_ _) k) (f' : ∀ α, SecBT D' (𝟙_ _) k α), U'.ExpT (𝟙_ _) k σ' f' ∧ (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') ∧ ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, gw C.v (r' ≫ famφT D' (𝟙_ _) α i) z (J (r' ≫ famφT D' (𝟙_ _) α i ≫ C.β)) (J' (r' ≫ famφT D' (𝟙_ _) α i)) ^ DegPre.famε k i).val * sval (f' α) r' z J' := by sorry
