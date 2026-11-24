-- Prove2me | Theorems.Thm_GlobalTheory_VFComp_coefVF_contDiffOn
-- name    : GlobalTheory.VFComp.coefVF_contDiffOn
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:50:50.285052+00:00
-- url     : https://prove2.me/theorems/c2218914-3f78-4f58-90a2-3dd3a7100ca2
-- title:
--   VFComp: coef VF cont Diff On
-- statement:
--   The VFComp construction uses the coef VF cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L47-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L47-L64

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

theorem GlobalTheory.VFComp.coefVF_contDiffOn {U : Set (E d)} (hU : IsOpen U) (m : ℕ)
    (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) (hc : ∀ j, ContDiffOn ℝ ∞ (c j) U) (n : ℕ) (w : Fin n → Fin d) :
    ContDiffOn ℝ ∞ (coefVF m a c n w) U := by sorry
