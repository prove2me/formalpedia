-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_tangent_fst
-- name    : GlobalTheory.TangentOrigin.tangent_fst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:30.89965+00:00
-- url     : https://prove2.me/theorems/a7aee8a9-b8bd-421d-b569-fa8b070c02d3
-- title:
--   Tangent Origin: tangent fst
-- statement:
--   The Tangent Origin construction uses the tangent fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L257-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L257-L264

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

theorem GlobalTheory.TangentOrigin.tangent_fst {v : epsR ℂ ⟶ A} (hv : IsTangent v) {W : A.left.Opens}
    (h : ⊤ ≤ v.left ⁻¹ᵁ W) (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (f : Γ(A.left, W)) :
    (evalPt (R := DualNumber ℂ) v.left W h f).fst = evalPt (u.ex 0).left W h0 f := by sorry
