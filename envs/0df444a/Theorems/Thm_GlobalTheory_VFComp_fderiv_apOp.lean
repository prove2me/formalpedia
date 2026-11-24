-- Prove2me | Theorems.Thm_GlobalTheory_VFComp_fderiv_apOp
-- name    : GlobalTheory.VFComp.fderiv_apOp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:52:14.986694+00:00
-- url     : https://prove2.me/theorems/40060071-51b4-4eed-879f-d7f93cb8872c
-- title:
--   VFComp: fderiv ap Op
-- statement:
--   The VFComp construction uses the fderiv ap Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L80-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L80-L98

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

theorem GlobalTheory.VFComp.fderiv_apOp {U : Set (E d)} (hU : IsOpen U) (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) {x : E d} (hx : x ∈ U)
    (j : Fin d) :
    fderiv ℝ (apOp m a u) x (ev j) = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      (fderiv ℝ (a n w) x (ev j) * dw (List.ofFn w) u x + a n w x * dw (j :: List.ofFn w) u x) := by sorry
