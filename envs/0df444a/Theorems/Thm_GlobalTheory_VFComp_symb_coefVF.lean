-- Prove2me | Theorems.Thm_GlobalTheory_VFComp_symb_coefVF
-- name    : GlobalTheory.VFComp.symb_coefVF
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:50:40.547255+00:00
-- url     : https://prove2.me/theorems/eae750c4-ae12-4243-bbc4-32ea17b3e420
-- title:
--   VFComp: symb coef VF
-- statement:
--   The VFComp construction uses the symb coef VF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L66-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L66-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
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
open GlobalTheory GlobalTheory.VFComp
variable {d : ℕ}

theorem GlobalTheory.VFComp.symb_coefVF (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (x ξ : E d) : symb (m + 1) (coefVF m a c) x ξ = (∑ j, c j x * ((ξ j : ℝ) : ℂ)) * symb m a x ξ := by sorry
