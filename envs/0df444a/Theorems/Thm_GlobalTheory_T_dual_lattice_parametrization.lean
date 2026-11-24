-- Prove2me | Theorems.Thm_GlobalTheory_T_dual_lattice_parametrization
-- name    : GlobalTheory.T.dual_lattice_parametrization
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:32:47.423921+00:00
-- url     : https://prove2.me/theorems/3abd9742-93c4-4fd3-876d-e3626144da2e
-- title:
--   T: dual lattice parametrization
-- statement:
--   The T construction uses the dual lattice parametrization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DualLatticeParametrizationStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DualLatticeParametrizationStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DualLatticeParametrization
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DualLatticeParametrizationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.dual_lattice_parametrization : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), B.det ≠ 0 → 0 < N → ∃ e : (ι × InfinitePlace F → ℤ) → ι → F, (∀ n i v, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ e n) i) = n (i, v)) ∧ ∀ y : ι → F, (∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m) → ∃ n, e n = y := by sorry
