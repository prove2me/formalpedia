-- Prove2me | Theorems.Thm_GlobalTheory_RigSq_gm_sq_g
-- name    : GlobalTheory.RigSq.gm_sq_g
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:24.32783+00:00
-- url     : https://prove2.me/theorems/85e9fe06-5c76-4b20-b96d-ba4586603b10
-- title:
--   Rig Sq: gm sq g
-- statement:
--   The Rig Sq construction uses the gm sq g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRescaleRigidifiedSquareIso.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRescaleRigidifiedSquareIso.lean#L17-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRescaleRigidifiedSquareIso
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
noncomputable section
open GlobalTheory GlobalTheory.RigSq
variable {X Y : Scheme.{0}}

theorem GlobalTheory.RigSq.gm_sq_g (L : LB X) (f : Y ⟶ X) (y : Y) (j j' : L.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ 2 := by sorry
