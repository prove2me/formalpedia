-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_isDiff_iff
-- name    : GlobalTheory.TangentOrigin.isDiff_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:07.521808+00:00
-- url     : https://prove2.me/theorems/678905d4-b78a-4e45-bc42-6e7259659002
-- title:
--   Tangent Origin: is Diff iff
-- statement:
--   The Tangent Origin construction uses the is Diff iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L273-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L273-L299

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.TangentOrigin
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
variable {u}

theorem GlobalTheory.TangentOrigin.isDiff_iff {v : epsR ℂ ⟶ A} (hv : IsTangent v) {U : A.left.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (w : Fin g → ℂ) :
    u.IsDiff w v ↔ evalPt (R := DualNumber ℂ) v.left U h = jet u w U h0 := by sorry
