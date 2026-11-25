-- Prove2me | Theorems.Thm_GlobalTheory_CoordToExt_exists_rig
-- name    : GlobalTheory.CoordToExt.exists_rig
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:35:19.787799+00:00
-- url     : https://prove2.me/theorems/2c8338cf-e2c6-4874-9136-7226603f4962
-- title:
--   Coord To Ext: exists rig
-- statement:
--   The Coord To Ext construction uses the exists rig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAbelianSchemeThick.lean#L121-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAbelianSchemeThick.lean#L121-L141

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CoordToExt
variable {S : Scheme.{0}}

theorem GlobalTheory.CoordToExt.exists_rig {G B T : Scheme.{0}} (q : G ⟶ B) (eG : T ⟶ G) (eB : T ⟶ B) (e : eG ≫ q = eB) (M : LB B)
    (s : ∀ a : M.ι, Γ(G, q ⁻¹ᵁ M.U a)ˣ)
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (a a' : M.ι), q (r z) ∈ M.U a → q (r z) ∈ M.U a' →
      gm r z _ (s a') = gm (r ≫ q) z _ (M.g a a') * gm r z _ (s a)) :
    ∃ ρ : LB.Gen (M.pull eB), ρ.IsGen ∧ ∀ (a : M.ι) (y : T), q (eG y) ∈ M.U a →
      gm eG y _ (s a) * gm (𝟙 _) y _ (ρ.s fun _ => a) = 1 := by sorry
