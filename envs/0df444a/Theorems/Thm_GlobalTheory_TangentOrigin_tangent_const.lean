-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_tangent_const
-- name    : GlobalTheory.TangentOrigin.tangent_const
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:01:57.026453+00:00
-- url     : https://prove2.me/theorems/df9f203f-a034-4f8c-8e57-dd61df45d07a
-- title:
--   Tangent Origin: tangent const
-- statement:
--   The Tangent Origin construction uses the tangent const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L266-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L266-L271

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

theorem GlobalTheory.TangentOrigin.tangent_const (v : epsR ℂ ⟶ A) {W : A.left.Opens} (h : ⊤ ≤ v.left ⁻¹ᵁ W) (a : ℂ) :
    evalPt (R := DualNumber ℂ) v.left W h (constFn A.hom W a) = algebraMap ℂ (DualNumber ℂ) a := by sorry
