-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_lattice_sum
-- name    : GlobalTheory.CompanionTheory.SW.LatSum.lattice_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:06:47.920928+00:00
-- url     : https://prove2.me/theorems/64a7992a-74c3-45c4-bbe7-d1ae37e95083
-- title:
--   Lat Sum: lattice sum
-- statement:
--   The Lat Sum construction uses the lattice sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L204-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L204-L252

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum

theorem GlobalTheory.CompanionTheory.SW.LatSum.lattice_sum : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∀ M : ℕ, 2 ≤ M → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) →
      Summable (fun r : 𝓞 F => (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹) ∧
      ∑' r : 𝓞 F, (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹ ≤ C * ∏ w, (τ w).im * ((τ w).im ^ M)⁻¹ := by sorry
