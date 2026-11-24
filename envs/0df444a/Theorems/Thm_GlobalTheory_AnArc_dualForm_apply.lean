-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_dualForm_apply
-- name    : GlobalTheory.AnArc.dualForm_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:38:37.070675+00:00
-- url     : https://prove2.me/theorems/c987d074-a2c0-4a4b-ad9e-e755f4f295b0
-- title:
--   An Arc: dual Form apply
-- statement:
--   The An Arc construction uses the dual Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L285-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L285-L286

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
open Classical

theorem GlobalTheory.AnArc.dualForm_apply (w : ℂ) (r r' : A.X →+ ℂ) :
    A.dualForm w r r' = A.coord r ⬝ᵥ ((A.BwMat w)⁻¹.map Complex.ofReal) *ᵥ star (A.coord r') := by sorry
