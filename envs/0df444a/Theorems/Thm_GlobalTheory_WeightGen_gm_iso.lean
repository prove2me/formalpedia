-- Prove2me | Theorems.Thm_GlobalTheory_WeightGen_gm_iso
-- name    : GlobalTheory.WeightGen.gm_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:11.240503+00:00
-- url     : https://prove2.me/theorems/99c7e4e7-77c8-4196-9f4d-9b4bfe770e6e
-- title:
--   Weight Gen: gm iso
-- statement:
--   The Weight Gen construction uses the gm iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L76-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
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
open GlobalTheory GlobalTheory.WeightGen
variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)
variable {q a p}

theorem GlobalTheory.WeightGen.gm_iso {L M : LB B} {w : LB.Iso L M} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ B) (z : Z)
    {j j' : M.ι} {k k' : L.ι} (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') (hk : r z ∈ L.U k)
    (hk' : r z ∈ L.U k') :
    gm r z (M.U j ⊓ L.U k) (w.s (j, k)) = gm r z _ (M.g j j') * (gm r z _ (L.g k k'))⁻¹ *
      gm r z (M.U j' ⊓ L.U k') (w.s (j', k')) := by sorry
