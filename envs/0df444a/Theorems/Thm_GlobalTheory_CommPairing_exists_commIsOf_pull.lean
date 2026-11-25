-- Prove2me | Theorems.Thm_GlobalTheory_CommPairing_exists_commIsOf_pull
-- name    : GlobalTheory.CommPairing.exists_commIsOf_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:33.141715+00:00
-- url     : https://prove2.me/theorems/4b91de72-86f6-4161-a0ff-4e77a3898497
-- title:
--   Comm Pairing: exists comm Is Of pull
-- statement:
--   The Comm Pairing construction uses the exists comm Is Of pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsAlternatingSkewNatural.lean#L142-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsAlternatingSkewNatural.lean#L142-L159

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem GlobalTheory.CommPairing.exists_commIsOf_pull (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T) {θx θy : ThetaGrp A L k T}
    {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k θx θy c) :
    ∃ θx' θy' : ThetaGrp A L k T', θx'.pt = h ≫ θx.pt ∧ θy'.pt = h ≫ θy.pt ∧
      CommIsOf A L k θx' θy' (Units.map h.left.appTop.hom.toMonoidHom c) := by sorry
