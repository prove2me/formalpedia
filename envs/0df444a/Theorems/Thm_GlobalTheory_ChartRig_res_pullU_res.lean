-- Prove2me | Theorems.Thm_GlobalTheory_ChartRig_res_pullU_res
-- name    : GlobalTheory.ChartRig.res_pullU_res
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:21.446309+00:00
-- url     : https://prove2.me/theorems/57a0b6e9-187d-4474-9550-1ba5f784493e
-- title:
--   Chart Rig: res pull U res
-- statement:
--   The Chart Rig construction uses the res pull U res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RigidifiedOfChart.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RigidifiedOfChart.lean#L24-L31

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

theorem GlobalTheory.ChartRig.res_pullU_res (f : Y ⟶ X) (U U' : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U') (h' : U' ≤ U)
    (h'' : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU f U' (res h' x)) = res h'' (pullU f U x) := by sorry
