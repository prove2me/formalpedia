-- Prove2me | Theorems.Thm_GlobalTheory_PeriodVol_reImCoord_inl
-- name    : GlobalTheory.PeriodVol.reImCoord_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:56.126945+00:00
-- url     : https://prove2.me/theorems/13ab1715-8f58-4249-96d0-099c2c8e7bf9
-- title:
--   Period Vol: re Im Coord inl
-- statement:
--   The Period Vol construction uses the re Im Coord inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/VolumeFundamentalDomainPeriodLattice.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/VolumeFundamentalDomainPeriodLattice.lean#L19-L19

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

theorem GlobalTheory.PeriodVol.reImCoord_inl {g : ℕ} (z : Fin g → ℂ) (i : Fin g) : reImCoord g z (Sum.inl i) = (z i).re := by sorry

attribute [defeq] GlobalTheory.PeriodVol.reImCoord_inl
