-- Prove2me | Theorems.Thm_GlobalTheory_T_schur_function_compact_support_modulo_unipotent
-- name    : GlobalTheory.T.schur_function_compact_support_modulo_unipotent
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:56:36.035617+00:00
-- url     : https://prove2.me/theorems/d2c33d8d-f127-4e2d-986d-590d3b7c9a3f
-- title:
--   T: schur function compact support modulo unipotent
-- statement:
--   The T construction uses the schur function compact support modulo unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotentStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotentStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotentStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schur_function_compact_support_modulo_unipotent : ∀ (κ : Type) [Fintype κ] (m : Measure (κ → ℝ)), IsFiniteMeasure m → Integrable (fun x : κ → ℝ => ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m) → ∃ D : (κ → ℝ) → ℝ, Continuous D ∧ (∀ y, 0 ≤ D y) ∧ (∀ y, (D y : ℂ) = ∫ x : κ → ℝ, (∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, y w * x w : ℝ) : ℂ))) ∧ ∀ U : Set (κ → ℝ), MeasurableSet U → m U = ∫⁻ y in U, ENNReal.ofReal (D y) := by sorry
