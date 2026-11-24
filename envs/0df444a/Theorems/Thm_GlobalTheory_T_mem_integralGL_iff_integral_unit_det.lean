-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_integralGL_iff_integral_unit_det
-- name    : GlobalTheory.T.mem_integralGL_iff_integral_unit_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:20.979912+00:00
-- url     : https://prove2.me/theorems/cc669c58-cf2a-4f0e-9855-751864875fa5
-- title:
--   T: mem integral GL iff integral unit det
-- statement:
--   The T construction uses the mem integral GL iff integral unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemIntegralGLIffIntegralUnitDetStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemIntegralGLIffIntegralUnitDetStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_integralGL_iff_integral_unit_det : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (g : GL (Fin n) F), g ∈ GLint O n ↔ (IsInt O (g : Matrix (Fin n) (Fin n) F) ∧ nrm (g : Matrix (Fin n) (Fin n) F).det = 1) := by sorry
