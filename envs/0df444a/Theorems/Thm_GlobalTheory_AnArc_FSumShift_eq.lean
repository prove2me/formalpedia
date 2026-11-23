-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_FSumShift_eq
-- name    : GlobalTheory.AnArc.FSumShift_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:12.716772+00:00
-- url     : https://prove2.me/theorems/f8e20c91-64f8-4b9a-8ce5-4e0ddc98f995
-- title:
--   An Arc: FSum Shift eq
-- statement:
--   The An Arc construction uses the FSum Shift eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L428-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L428-L434

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

theorem GlobalTheory.AnArc.FSumShift_eq (la : A.La) {α : A.X} {m : ℤ} (hm : A.be la.y α = k * m) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSumShift k α th la v =
      HahnSeries.single m (Complex.exp (A.lin la v)) * A.FSum k (α + la.y) (A.shift k la α th) v := by sorry
