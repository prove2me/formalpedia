-- Prove2me | Theorems.Thm_GlobalTheory_FibLine_Intg_integrable_fsDens
-- name    : GlobalTheory.FibLine.Intg.integrable_fsDens
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:29.600322+00:00
-- url     : https://prove2.me/theorems/d6c10903-98f7-4cff-8b06-a01cda8f3df4
-- title:
--   Intg: integrable fs Dens
-- statement:
--   The Intg construction uses the integrable fs Dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableProdQCoefMulFsDens.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableProdQCoefMulFsDens.lean#L12-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine GlobalTheory.FibLine.Intg

theorem GlobalTheory.FibLine.Intg.integrable_fsDens : Integrable fsDens := by sorry
