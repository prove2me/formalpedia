-- Prove2me | Theorems.Thm_GlobalTheory_CommutatorPairing_commIsOf_iff
-- name    : GlobalTheory.CommutatorPairing.commIsOf_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:10.827801+00:00
-- url     : https://prove2.me/theorems/cd7295d1-84fb-4d3f-8eb6-4b4ee16d8fb5
-- title:
--   Commutator Pairing: comm Is Of iff
-- statement:
--   The Commutator Pairing construction uses the comm Is Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueWeilIs.lean#L130-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueWeilIs.lean#L130-L144

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
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
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}

theorem GlobalTheory.CommutatorPairing.commIsOf_iff (hL : L.IsLB) {T : Over S} (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) :
    CommIsOf A L k θx θy c ↔ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J), Good L z J →
      commVal θx θy t a z J = gm t.left z ⊤ c := by sorry
