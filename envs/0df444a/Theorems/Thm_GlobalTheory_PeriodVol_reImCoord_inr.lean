-- Prove2me | Theorems.Thm_GlobalTheory_PeriodVol_reImCoord_inr
-- name    : GlobalTheory.PeriodVol.reImCoord_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:22.766531+00:00
-- url     : https://prove2.me/theorems/5cba0e32-a68a-45f8-953d-7b42797bc303
-- title:
--   Period Vol: re Im Coord inr
-- statement:
--   The Period Vol construction uses the re Im Coord inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/VolumeFundamentalDomainPeriodLattice.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/VolumeFundamentalDomainPeriodLattice.lean#L21-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_VolumeFundamentalDomainPeriodLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodVol

theorem GlobalTheory.PeriodVol.reImCoord_inr {g : ℕ} (z : Fin g → ℂ) (i : Fin g) : reImCoord g z (Sum.inr i) = (z i).im := by sorry

attribute [defeq] GlobalTheory.PeriodVol.reImCoord_inr
