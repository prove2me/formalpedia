-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_Sum_add_Pw_div
-- name    : GlobalTheory.AnArc.Sum_add_Pw_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:40.547947+00:00
-- url     : https://prove2.me/theorems/f4d97762-63c9-4f27-ad56-aeaa9b263e1d
-- title:
--   An Arc: Sum add Pw div
-- statement:
--   The An Arc construction uses the Sum add Pw div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L415-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L415-L418

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
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
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable (k : ℕ) [NeZero k]

theorem GlobalTheory.AnArc.Sum_add_Pw_div (w : ℂ) (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.Sum k α th w (v + (k : ℂ)⁻¹ • A.Pw w la) = Complex.exp (A.lin la v) * eTwoPi (w * A.be la.y α / k) *
      A.Sum k (α + la.y) (A.shift k la α th) w v := by sorry
