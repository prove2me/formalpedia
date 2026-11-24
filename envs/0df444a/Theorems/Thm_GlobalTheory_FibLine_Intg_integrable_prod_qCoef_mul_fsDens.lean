-- Prove2me | Theorems.Thm_GlobalTheory_FibLine_Intg_integrable_prod_qCoef_mul_fsDens
-- name    : GlobalTheory.FibLine.Intg.integrable_prod_qCoef_mul_fsDens
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:23:23.898748+00:00
-- url     : https://prove2.me/theorems/4822278c-9d41-4f06-8292-21be8599e800
-- title:
--   Intg: integrable prod q Coef mul fs Dens
-- statement:
--   The Intg construction uses the integrable prod q Coef mul fs Dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableProdQCoefMulFsDens.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableProdQCoefMulFsDens.lean#L48-L54

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

theorem GlobalTheory.FibLine.Intg.integrable_prod_qCoef_mul_fsDens (k : ℕ) (f : Fin k → Fin 2 × Fin 2) :
    Integrable (fun x : ℂ => (∏ i, qCoef x (f i)) * (fsDens x : ℂ)) := by sorry
