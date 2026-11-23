-- Prove2me | Theorems.Thm_GlobalTheory_PeriodVol_reImCoord_symm_re
-- name    : GlobalTheory.PeriodVol.reImCoord_symm_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:20.239626+00:00
-- url     : https://prove2.me/theorems/6528322f-0c84-4c8e-bdd5-d091bc201a74
-- title:
--   Period Vol: re Im Coord symm re
-- statement:
--   The Period Vol construction uses the re Im Coord symm re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/VolumeFundamentalDomainPeriodLattice.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/VolumeFundamentalDomainPeriodLattice.lean#L23-L24

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

theorem GlobalTheory.PeriodVol.reImCoord_symm_re {g : ℕ} (p : Fin g ⊕ Fin g → ℝ) (i : Fin g) :
    ((reImCoord g).symm p i).re = p (Sum.inl i) := by sorry

attribute [defeq] GlobalTheory.PeriodVol.reImCoord_symm_re
