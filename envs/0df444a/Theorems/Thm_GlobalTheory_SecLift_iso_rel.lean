-- Prove2me | Theorems.Thm_GlobalTheory_SecLift_iso_rel
-- name    : GlobalTheory.SecLift.iso_rel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:00.461991+00:00
-- url     : https://prove2.me/theorems/4799004d-445d-4d1a-822e-ba4b86db2b54
-- title:
--   Sec Lift: iso rel
-- statement:
--   The Sec Lift construction uses the iso rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L185-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L185-L193

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]
variable {N : LB X} {N' : LB Y} {F : Y ⟶ X}

theorem GlobalTheory.SecLift.iso_rel {w : LB.Iso N' (N.pull F)} (hw : w.IsGen) (y : Y) {k l : N.ι} {k' l' : N'.ι}
    (hk : F y ∈ N.U k) (hl : F y ∈ N.U l) (hk' : y ∈ N'.U k') (hl' : y ∈ N'.U l') :
    (Geo.Tor.gw w (𝟙 Y) y k k').val * gr (𝟙 Y) y (N'.U k' ⊓ N'.U l') ⟨hk', hl'⟩ (N'.g k' l').val =
      gr (𝟙 Y ≫ F) y (N.U k ⊓ N.U l) ⟨hk, hl⟩ (N.g k l).val * (Geo.Tor.gw w (𝟙 Y) y l l').val := by sorry
