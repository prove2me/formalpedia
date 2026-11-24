-- Prove2me | Theorems.Thm_GlobalTheory_VFComp_apOp_coefVF
-- name    : GlobalTheory.VFComp.apOp_coefVF
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:50:56.915826+00:00
-- url     : https://prove2.me/theorems/5fe24363-151c-4a96-836c-cf25ae9982b6
-- title:
--   VFComp: ap Op coef VF
-- statement:
--   The VFComp construction uses the ap Op coef VF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L105-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L105-L150

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

theorem GlobalTheory.VFComp.apOp_coefVF {U : Set (E d)} (hU : IsOpen U) (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (c : Fin d → E d → ℂ) (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U)
    {x : E d} (hx : x ∈ U) :
    ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) = apOp (m + 1) (coefVF m a c) u x := by sorry
