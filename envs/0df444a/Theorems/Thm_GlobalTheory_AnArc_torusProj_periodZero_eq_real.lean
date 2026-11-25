-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_torusProj_periodZero_eq_real
-- name    : GlobalTheory.AnArc.torusProj_periodZero_eq_real
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:01.697031+00:00
-- url     : https://prove2.me/theorems/fe60121e-e2b5-4846-aa23-a5ea20269719
-- title:
--   An Arc: torus Proj period Zero eq real
-- statement:
--   The An Arc construction uses the torus Proj period Zero eq real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L223-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L223-L228

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.torusProj_periodZero_eq_real (n : A.X →+ ℤ) (l : A.abelian₂) (x : A.X) :
    A.torusProj (A.P0 (La.mk 0 n l)) x = ((n x + (A.H l (A.ct x)).im : ℝ) : ℂ) := by sorry
