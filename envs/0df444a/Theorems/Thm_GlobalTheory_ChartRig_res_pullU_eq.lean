-- Prove2me | Theorems.Thm_GlobalTheory_ChartRig_res_pullU_eq
-- name    : GlobalTheory.ChartRig.res_pullU_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:14.584972+00:00
-- url     : https://prove2.me/theorems/ae1d0bef-77f7-4609-ab83-9017c6c66b80
-- title:
--   Chart Rig: res pull U eq
-- statement:
--   The Chart Rig construction uses the res pull U eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RigidifiedOfChart.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RigidifiedOfChart.lean#L11-L14

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

theorem GlobalTheory.ChartRig.res_pullU_eq (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU f U x) = Units.map (f.appLE U V h).hom.toMonoidHom x := by sorry
