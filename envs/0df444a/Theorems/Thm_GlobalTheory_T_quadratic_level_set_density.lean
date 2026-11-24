-- Prove2me | Theorems.Thm_GlobalTheory_T_quadratic_level_set_density
-- name    : GlobalTheory.T.quadratic_level_set_density
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:56.593924+00:00
-- url     : https://prove2.me/theorems/4193ff8c-61c0-4a63-861c-66d88b26c7f0
-- title:
--   T: quadratic level set density
-- statement:
--   The T construction uses the quadratic level set density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuadraticLevelSetDensityStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuadraticLevelSetDensityStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuadraticLevelSetDensity
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuadraticLevelSetDensityStatement
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

theorem GlobalTheory.T.quadratic_level_set_density : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∃ Di : (InfinitePlace F → ℝ) → ℝ, Continuous Di ∧ (∀ y, 0 ≤ Di y) ∧ (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (P w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Di y)) ∧ Integrable (fun x : InfinitePlace F → ℝ => cG B ρ P (fun w => (x w : ℂ) + Complex.I)) ∧ ∀ z : InfinitePlace F → ℝ, ∫ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) = ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| * Di z : ℝ) : ℂ) := by sorry
