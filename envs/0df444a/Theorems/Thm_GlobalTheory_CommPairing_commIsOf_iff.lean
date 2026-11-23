-- Prove2me | Theorems.Thm_GlobalTheory_CommPairing_commIsOf_iff
-- name    : GlobalTheory.CommPairing.commIsOf_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:55.631652+00:00
-- url     : https://prove2.me/theorems/711662b0-845b-482e-b005-fc8e8fa58700
-- title:
--   Comm Pairing: comm Is Of iff
-- statement:
--   The Comm Pairing construction uses the comm Is Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsAlternatingSkewNatural.lean#L58-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsAlternatingSkewNatural.lean#L58-L73

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

theorem GlobalTheory.CommPairing.commIsOf_iff (hL : L.IsLB) {T : Over S} (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) :
    CommIsOf A L k θx θy c ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval θx r z J * tval θy (r ≫ (translT A θx.pt).left) z J =
        tval θy r z J * tval θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c := by sorry
