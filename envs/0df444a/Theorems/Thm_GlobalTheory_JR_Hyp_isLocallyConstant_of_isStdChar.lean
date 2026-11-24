-- Prove2me | Theorems.Thm_GlobalTheory_JR_Hyp_isLocallyConstant_of_isStdChar
-- name    : GlobalTheory.JR.Hyp.isLocallyConstant_of_isStdChar
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:33:33.994811+00:00
-- url     : https://prove2.me/theorems/6cbe6b21-a558-400e-865f-92d42fd9d81a
-- title:
--   Hyp: is Locally Constant of is Std Char
-- statement:
--   The Hyp construction uses the is Locally Constant of is Std Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantEtaleTraceAddCharHermitianKerne.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantEtaleTraceAddCharHermitianKerne.lean#L8-L15

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantEtaleTraceAddCharHermitianKerne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp

theorem GlobalTheory.JR.Hyp.isLocallyConstant_of_isStdChar {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ)
    (hψ : IsStdChar ψ) : IsLocallyConstant (fun t : F => ψ t) := by sorry
