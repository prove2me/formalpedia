-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_jet_snd
-- name    : GlobalTheory.TangentOrigin.jet_snd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:44.234228+00:00
-- url     : https://prove2.me/theorems/fb92f87c-95c8-4552-969e-0d20cdcf0648
-- title:
--   Tangent Origin: jet snd
-- statement:
--   The Tangent Origin construction uses the jet snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L223-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L223-L225

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

theorem GlobalTheory.TangentOrigin.jet_snd (w : Fin g → ℂ) (W : A.left.Opens) (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W)
    (f : Γ(A.left, W)) :
    (jet u w W h f).snd = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w := by sorry
