-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_dualForm_re_im
-- name    : GlobalTheory.AnArc.dualForm_re_im
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:40:21.338461+00:00
-- url     : https://prove2.me/theorems/9d48b25e-6dc1-4c1b-9511-f879a58b784f
-- title:
--   An Arc: dual Form re im
-- statement:
--   The An Arc construction uses the dual Form re im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L317-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L317-L325

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

theorem GlobalTheory.AnArc.dualForm_re_im (w : ℂ) (r r' : A.X →+ ℂ) (M : Matrix _ _ ℝ) (hM : M = by classical exact (A.BwMat w)⁻¹) :
    (A.dualForm w r r').re = (fun i => (A.coord r i).re) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).re) +
      (fun i => (A.coord r i).im) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).im) ∧
    (A.dualForm w r r').im = (fun i => (A.coord r i).im) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).re) -
      (fun i => (A.coord r i).re) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).im) := by sorry
