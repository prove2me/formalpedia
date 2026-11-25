-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_hasSum_add_Pw
-- name    : GlobalTheory.AnArc.hasSum_add_Pw
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:33.65866+00:00
-- url     : https://prove2.me/theorems/153af0af-0bba-5933-b64b-5bf39fe9c4cc
-- title:
--   An Arc: has Sum add Pw
-- statement:
--   The An Arc construction uses the has Sum add Pw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L181-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L181-L185

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

theorem GlobalTheory.AnArc.hasSum_add_Pw {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (w : ℂ)
    (la : A.La) (v : A.V) {s : ℂ} (hs : HasSum (fun μ => A.term j α th μ v * eTwoPi (w * A.exponent j α μ)) s) :
    HasSum (fun μ => A.term j α th μ (v + A.Pw w la) * eTwoPi (w * A.exponent j α μ)) (A.perFactor w la v ^ j * s) := by sorry
