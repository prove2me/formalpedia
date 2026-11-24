-- Prove2me | Theorems.Thm_GlobalTheory_HCA_dw_hasCompactSupport_tsupport
-- name    : GlobalTheory.HCA.dw_hasCompactSupport_tsupport
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:59:30.53845+00:00
-- url     : https://prove2.me/theorems/c7e1334c-72ab-4096-b635-f8d8fa868393
-- title:
--   HCA: dw has Compact Support tsupport
-- statement:
--   The HCA construction uses the dw has Compact Support tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeakSolutionOfSmoothSolution.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeakSolutionOfSmoothSolution.lean#L29-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeakSolutionOfSmoothSolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction Topology
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.dw_hasCompactSupport_tsupport {d : ℕ} (w : List (Fin d)) {f : E d → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (dw w f) ∧ tsupport (dw w f) ⊆ tsupport f := by sorry
