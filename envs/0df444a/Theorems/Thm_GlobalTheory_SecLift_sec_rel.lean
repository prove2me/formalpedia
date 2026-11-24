-- Prove2me | Theorems.Thm_GlobalTheory_SecLift_sec_rel
-- name    : GlobalTheory.SecLift.sec_rel
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:11.619808+00:00
-- url     : https://prove2.me/theorems/3f298d4d-cf97-4bee-b18a-f09808283e77
-- title:
--   Sec Lift: sec rel
-- statement:
--   The Sec Lift construction uses the sec rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L202-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L202-L206

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

theorem GlobalTheory.SecLift.sec_rel (s : LB.Sec N) (x : X) {k l : N.ι} (hk : x ∈ N.U k) (hl : x ∈ N.U l) :
    gr (𝟙 X) x _ hk (s.f k) =
      gr (𝟙 X) x (N.U k ⊓ N.U l) ⟨hk, hl⟩ (N.g k l).val * gr (𝟙 X) x _ hl (s.f l) := by sorry
