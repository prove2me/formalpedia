-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_evalPt_ex_const
-- name    : GlobalTheory.TangentOrigin.evalPt_ex_const
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:06.656162+00:00
-- url     : https://prove2.me/theorems/b5656e62-ef2d-4b40-9fa6-163e73fc86f7
-- title:
--   Tangent Origin: eval Pt ex const
-- statement:
--   The Tangent Origin construction uses the eval Pt ex const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L233-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L233-L239

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

theorem GlobalTheory.TangentOrigin.evalPt_ex_const (z : Fin g → ℂ) {W : A.left.Opens} (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W) (a : ℂ) :
    evalPt (u.ex z).left W h (constFn A.hom W a) = a := by sorry
