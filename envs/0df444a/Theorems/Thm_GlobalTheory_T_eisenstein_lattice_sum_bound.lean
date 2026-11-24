-- Prove2me | Theorems.Thm_GlobalTheory_T_eisenstein_lattice_sum_bound
-- name    : GlobalTheory.T.eisenstein_lattice_sum_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:33:02.666526+00:00
-- url     : https://prove2.me/theorems/10dc32d5-7eed-496e-b718-e28a047962e1
-- title:
--   T: eisenstein lattice sum bound
-- statement:
--   The T construction uses the eisenstein lattice sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBoundStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBoundStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBoundStatement
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

theorem GlobalTheory.T.eisenstein_lattice_sum_bound : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ M : ℕ, 2 ≤ M → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) → Summable (fun r : 𝓞 F => (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹) ∧ ∑' r : 𝓞 F, (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹ ≤ C * ∏ w, (τ w).im * ((τ w).im ^ M)⁻¹ := by sorry
