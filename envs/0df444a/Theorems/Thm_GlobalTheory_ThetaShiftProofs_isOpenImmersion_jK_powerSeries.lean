-- Prove2me | Theorems.Thm_GlobalTheory_ThetaShiftProofs_isOpenImmersion_jK_powerSeries
-- name    : GlobalTheory.ThetaShiftProofs.isOpenImmersion_jK_powerSeries
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:07:48.02172+00:00
-- url     : https://prove2.me/theorems/be791484-a1f2-495c-a76f-230217d3ac16
-- title:
--   Theta Shift Proofs: is Open Immersion j K power Series
-- statement:
--   The Theta Shift Proofs construction uses the is Open Immersion j K power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsOpenImmersionJKPowerSeries.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsOpenImmersionJKPowerSeries.lean#L11-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsOpenImmersionJKPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaShiftProofs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.ThetaShiftProofs.isOpenImmersion_jK_powerSeries (k : Type) [Field k] : IsOpenImmersion (Out.jK (PowerSeries k)) := by sorry
