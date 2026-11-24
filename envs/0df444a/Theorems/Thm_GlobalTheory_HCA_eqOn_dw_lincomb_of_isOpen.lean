-- Prove2me | Theorems.Thm_GlobalTheory_HCA_eqOn_dw_lincomb_of_isOpen
-- name    : GlobalTheory.HCA.eqOn_dw_lincomb_of_isOpen
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:00:58.982868+00:00
-- url     : https://prove2.me/theorems/f54a6175-b2d6-4f03-87ad-a305e77a9340
-- title:
--   HCA: eq On dw lincomb of is Open
-- statement:
--   The HCA construction uses the eq On dw lincomb of is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DwSmoothLocalLinear.lean#L42-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DwSmoothLocalLinear.lean#L42-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
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

theorem GlobalTheory.HCA.eqOn_dw_lincomb_of_isOpen {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (w : List (Fin d))
    (u v : E d → ℂ) (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) (s t : ℂ) :
    Set.EqOn (dw w (s • u + t • v)) (s • dw w u + t • dw w v) U := by sorry
