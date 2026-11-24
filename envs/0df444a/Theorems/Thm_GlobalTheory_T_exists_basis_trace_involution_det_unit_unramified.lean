-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_basis_trace_involution_det_unit_unramified
-- name    : GlobalTheory.T.exists_basis_trace_involution_det_unit_unramified
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:33:40.54219+00:00
-- url     : https://prove2.me/theorems/c92458c7-933a-43d5-821b-25ab830e7fd7
-- title:
--   T: exists basis trace involution det unit unramified
-- statement:
--   The T construction uses the exists basis trace involution det unit unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBasisTraceInvolutionDetUnitUnramifiedStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBasisTraceInvolutionDetUnitUnramifiedStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisTraceInvolutionDetUnitUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisTraceInvolutionDetUnitUnramifiedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_basis_trace_involution_det_unit_unramified : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det ≠ 0 ∧ val K.O (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = 0 := by sorry
