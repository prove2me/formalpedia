-- Prove2me | Theorems.Thm_GlobalTheory_HCA_dw_perm
-- name    : GlobalTheory.HCA.dw_perm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:00:09.539039+00:00
-- url     : https://prove2.me/theorems/c3dffc2f-3d32-48a2-a13e-be6e139615ac
-- title:
--   HCA: dw perm
-- statement:
--   The HCA construction uses the dw perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L88-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L88-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow
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
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.dw_perm {d : ℕ} {U : Set (E d)} (hU : IsOpen U) {w₁ w₂ : List (Fin d)} (h : w₁.Perm w₂) :
    ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → Set.EqOn (dw w₁ u) (dw w₂ u) U := by sorry
