-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_fderiv_val_res
-- name    : GlobalTheory.TangentOrigin.fderiv_val_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:20.349995+00:00
-- url     : https://prove2.me/theorems/0a0346ec-612e-40da-b86b-358854cbbc49
-- title:
--   Tangent Origin: fderiv val res
-- statement:
--   The Tangent Origin construction uses the fderiv val res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L180-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L180-L186

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

theorem GlobalTheory.TangentOrigin.fderiv_val_res {W V : A.left.Opens} (e : V ≤ W) (hW : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W)
    (hV : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ V) (f : Γ(A.left, W)) :
    fderiv ℂ (fun z => valAt' (u.ex z).left V (resG A.left e f)) 0 =
      fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 := by sorry
