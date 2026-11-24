-- Prove2me | Theorems.Thm_GlobalTheory_HCA_contDiffOn_dw_of_isOpen
-- name    : GlobalTheory.HCA.contDiffOn_dw_of_isOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:59.33018+00:00
-- url     : https://prove2.me/theorems/9c0796bd-43b3-42db-b1a2-f948733cfcb9
-- title:
--   HCA: cont Diff On dw of is Open
-- statement:
--   The HCA construction uses the cont Diff On dw of is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DwSmoothLocalLinear.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DwSmoothLocalLinear.lean#L20-L28

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
open MeasureTheory
open scoped ContDiff BoundedContinuousFunction Topology

theorem GlobalTheory.HCA.contDiffOn_dw_of_isOpen {d : ℕ} {U : Set (_root_.ZetaZeros.D.EllReg.E d)} (hU : IsOpen U) (w : List (Fin d))
    (u : _root_.ZetaZeros.D.EllReg.E d → ℂ) (hu : ContDiffOn ℝ ∞ u U) : ContDiffOn ℝ ∞ (_root_.ZetaZeros.D.EllReg.dw w u) U := by sorry
