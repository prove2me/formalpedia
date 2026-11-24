-- Prove2me | Theorems.Thm_GlobalTheory_HCA_eqOn_dw_of_isOpen
-- name    : GlobalTheory.HCA.eqOn_dw_of_isOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:19.903265+00:00
-- url     : https://prove2.me/theorems/096ec87f-f1d9-4849-8234-bf75f97e16dd
-- title:
--   HCA: eq On dw of is Open
-- statement:
--   The HCA construction uses the eq On dw of is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DwSmoothLocalLinear.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DwSmoothLocalLinear.lean#L33-L40

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

theorem GlobalTheory.HCA.eqOn_dw_of_isOpen {d : ℕ} {U : Set (_root_.ZetaZeros.D.EllReg.E d)} (hU : IsOpen U) (w : List (Fin d))
    (u v : _root_.ZetaZeros.D.EllReg.E d → ℂ) (h : Set.EqOn u v U) : Set.EqOn (_root_.ZetaZeros.D.EllReg.dw w u) (_root_.ZetaZeros.D.EllReg.dw w v) U := by sorry
