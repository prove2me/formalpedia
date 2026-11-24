-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_FSum_add
-- name    : GlobalTheory.AnArc.FSum_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:56:52.648993+00:00
-- url     : https://prove2.me/theorems/60acf8ba-6d67-4889-9eb6-9b2e8c45caee
-- title:
--   An Arc: FSum add
-- statement:
--   The An Arc construction uses the FSum add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L221-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L221-L224

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

theorem GlobalTheory.AnArc.FSum_add (j : ℕ) [NeZero j] (α : A.X) (th th' : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum j α (th + th') v = A.FSum j α th v + A.FSum j α th' v := by sorry
