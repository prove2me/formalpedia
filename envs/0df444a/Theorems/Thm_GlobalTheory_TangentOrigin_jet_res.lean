-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_jet_res
-- name    : GlobalTheory.TangentOrigin.jet_res
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:11.129552+00:00
-- url     : https://prove2.me/theorems/dff9d7e6-67e6-4e87-9ff6-4d75c7e3e57e
-- title:
--   Tangent Origin: jet res
-- statement:
--   The Tangent Origin construction uses the jet res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L227-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L227-L231

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

theorem GlobalTheory.TangentOrigin.jet_res (w : Fin g → ℂ) {W V : A.left.Opens} (e : V ≤ W) (hW : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W)
    (hV : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ V) (f : Γ(A.left, W)) :
    jet u w V hV (resG A.left e f) = jet u w W hW f := by sorry
