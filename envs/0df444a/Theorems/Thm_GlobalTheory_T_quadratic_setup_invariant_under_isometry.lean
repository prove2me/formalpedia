-- Prove2me | Theorems.Thm_GlobalTheory_T_quadratic_setup_invariant_under_isometry
-- name    : GlobalTheory.T.quadratic_setup_invariant_under_isometry
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:55:36.935891+00:00
-- url     : https://prove2.me/theorems/0d34e98e-2c7d-4236-b09d-04d0f1e91a0b
-- title:
--   T: quadratic setup invariant under isometry
-- statement:
--   The T construction uses the quadratic setup invariant under isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuadraticSetupInvariantUnderIsometryStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuadraticSetupInvariantUnderIsometryStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuadraticSetupInvariantUnderIsometry
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuadraticSetupInvariantUnderIsometryStatement
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

theorem GlobalTheory.T.quadratic_setup_invariant_under_isometry : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (gi : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → (∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) → QSetup M B ρ (fun w => (gi w)ᵀ * P w * gi w) := by sorry
