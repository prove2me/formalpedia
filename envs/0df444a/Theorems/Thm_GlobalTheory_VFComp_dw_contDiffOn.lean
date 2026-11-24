-- Prove2me | Theorems.Thm_GlobalTheory_VFComp_dw_contDiffOn
-- name    : GlobalTheory.VFComp.dw_contDiffOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:27.057058+00:00
-- url     : https://prove2.me/theorems/90acd143-ebf5-423a-a5f0-7680ad71d679
-- title:
--   VFComp: dw cont Diff On
-- statement:
--   The VFComp construction uses the dw cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean#L13-L18

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

theorem GlobalTheory.VFComp.dw_contDiffOn {U : Set (E d)} (hU : IsOpen U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) :
    ∀ w : List (Fin d), ContDiffOn ℝ ∞ (dw w u) U
  := by sorry
