-- Prove2me | Theorems.Thm_GlobalTheory_DiscClass_abs_norm_eq_norm_sq
-- name    : GlobalTheory.DiscClass.abs_norm_eq_norm_sq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:32.52838+00:00
-- url     : https://prove2.me/theorems/3da116c7-e616-40b4-a0ac-398460220e1c
-- title:
--   Disc Class: abs norm eq norm sq
-- statement:
--   The Disc Class construction uses the abs norm eq norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FractionalIdealNormPowSixMulDiscriminantClassInv.lean#L24-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FractionalIdealNormPowSixMulDiscriminantClassInv.lean#L24-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealNormPowSixMulDiscriminantClassInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DiscClass

theorem GlobalTheory.DiscClass.abs_norm_eq_norm_sq {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (h2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (x : K) :
    ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ‖φK x‖ ^ 2 := by sorry
