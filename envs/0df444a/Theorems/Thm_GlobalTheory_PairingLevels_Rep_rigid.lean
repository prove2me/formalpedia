-- Prove2me | Theorems.Thm_GlobalTheory_PairingLevels_Rep_rigid
-- name    : GlobalTheory.PairingLevels.Rep.rigid
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:45.812486+00:00
-- url     : https://prove2.me/theorems/d7cec3b7-2329-4a99-a6dd-9ca20a940169
-- title:
--   Rep: rigid
-- statement:
--   The Rep construction uses the rigid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L131-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L131-L144

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left)
variable {L} {Y : Over S} {D D' : FreeAbelianGroup (Y.left ⟶ A.left)} {f f' : ValFam L Y}

theorem GlobalTheory.PairingLevels.Rep.rigid (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {Z : Over S}
    {D : FreeAbelianGroup ((Z ⊗ A).left ⟶ A.left)} {f : ValFam L (Z ⊗ A)} (h : Rep L D f) (hD : D = 0)
    (a : Z ⟶ A) {z : Z.left} {J} (hJ : Good L z J) : f Z (lift (𝟙 Z) a) z J = f Z (lift (𝟙 Z) 1) z J := by sorry
