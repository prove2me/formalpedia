-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_Sum_add
-- name    : GlobalTheory.AnArc.Sum_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:05.811898+00:00
-- url     : https://prove2.me/theorems/2ff54fdb-615c-51f9-8b52-65e8e6c03b3b
-- title:
--   An Arc: Sum add
-- statement:
--   The An Arc construction uses the Sum add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L210-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L210-L214

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

theorem GlobalTheory.AnArc.Sum_add {j : ℕ} {α : A.X} {th th' : (Fin A.gB → ℂ) → ℂ} {w : ℂ} {v : A.V}
    (h : Summable fun μ => A.term j α th μ v * eTwoPi (w * A.exponent j α μ))
    (h' : Summable fun μ => A.term j α th' μ v * eTwoPi (w * A.exponent j α μ)) :
    A.Sum j α (th + th') w v = A.Sum j α th w v + A.Sum j α th' w v := by sorry
