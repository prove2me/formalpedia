-- Prove2me | Theorems.Thm_GlobalTheory_ChartRig_exists_gen_pull
-- name    : GlobalTheory.ChartRig.exists_gen_pull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:04.236779+00:00
-- url     : https://prove2.me/theorems/90bc390b-d6a1-4bac-a0d7-17a58282dabb
-- title:
--   Chart Rig: exists gen pull
-- statement:
--   The Chart Rig construction uses the exists gen pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RigidifiedOfChart.lean#L33-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RigidifiedOfChart.lean#L33-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RigidifiedOfChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartRig
variable {X Y : Scheme.{0}}

theorem GlobalTheory.ChartRig.exists_gen_pull (L : LB X) (f : Y ⟶ X) (i : L.ι) (hL : L.IsLB) (hi : ⊤ ≤ f ⁻¹ᵁ L.U i) :
    ∃ t : LB.Gen (L.pull f), t.IsGen := by sorry
