-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_FSum_eq_translate
-- name    : GlobalTheory.AnArc.FSum_eq_translate
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:56:51.875701+00:00
-- url     : https://prove2.me/theorems/56afb248-4d29-4cf1-a8f9-469faffb4e3e
-- title:
--   An Arc: FSum eq translate
-- statement:
--   The An Arc construction uses the FSum eq translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L248-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L248-L257

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

theorem GlobalTheory.AnArc.FSum_eq_translate (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (y : A.X) (v : A.V) :
    A.FSum j α th v = HahnSeries.single (A.exponent j α y) ((A.psi y : ℂ) ^ j * eTwoPi (A.T y α)) *
      A.FSum j (α + j • y) (fun z => th (z + A.ct y)) v := by sorry
