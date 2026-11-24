-- Prove2me | Theorems.Thm_GlobalTheory_HCA_SupEst_dw_zero_fun
-- name    : GlobalTheory.HCA.SupEst.dw_zero_fun
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:59:44.799295+00:00
-- url     : https://prove2.me/theorems/57b2eb6b-6ba5-4037-874e-5721a37e15b3
-- title:
--   Sup Est: dw zero fun
-- statement:
--   The Sup Est construction uses the dw zero fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticWeakSolWordDerivLeConstMulSup.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticWeakSolWordDerivLeConstMulSup.lean#L16-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticWeakSolWordDerivLeConstMulSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.HCA GlobalTheory.HCA.SupEst
variable {d : ℕ}

theorem GlobalTheory.HCA.SupEst.dw_zero_fun : ∀ w : List (Fin d), dw w (fun _ : E d => (0 : ℂ)) = fun _ => 0
  := by sorry
