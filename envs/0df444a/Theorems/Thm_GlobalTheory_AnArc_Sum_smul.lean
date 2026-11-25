-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_Sum_smul
-- name    : GlobalTheory.AnArc.Sum_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:19.602387+00:00
-- url     : https://prove2.me/theorems/6a408ee0-d146-550c-a6e0-2269c83b47ac
-- title:
--   An Arc: Sum smul
-- statement:
--   The An Arc construction uses the Sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L206-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L206-L208

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

theorem GlobalTheory.AnArc.Sum_smul (j : ℕ) (α : A.X) (c : ℂ) (th : (Fin A.gB → ℂ) → ℂ) (w : ℂ) (v : A.V) :
    A.Sum j α (c • th) w v = c * A.Sum j α th w v := by sorry
