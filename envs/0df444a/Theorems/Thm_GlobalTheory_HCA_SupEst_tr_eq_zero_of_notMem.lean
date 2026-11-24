-- Prove2me | Theorems.Thm_GlobalTheory_HCA_SupEst_tr_eq_zero_of_notMem
-- name    : GlobalTheory.HCA.SupEst.tr_eq_zero_of_notMem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:59:37.664809+00:00
-- url     : https://prove2.me/theorems/c75e3022-708d-455a-84f0-da6344d50843
-- title:
--   Sup Est: tr eq zero of not Mem
-- statement:
--   The Sup Est construction uses the tr eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticWeakSolWordDerivLeConstMulSup.lean#L24-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticWeakSolWordDerivLeConstMulSup.lean#L24-L35

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

theorem GlobalTheory.HCA.SupEst.tr_eq_zero_of_notMem {ι : Type} (P : Sys d ι) (i : ι) {φ : E d → ℂ} {x : E d}
    (hx : x ∉ tsupport φ) : P.tr i φ x = 0 := by sorry
