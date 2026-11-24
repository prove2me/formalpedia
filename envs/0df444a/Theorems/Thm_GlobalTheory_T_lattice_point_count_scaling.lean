-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_point_count_scaling
-- name    : GlobalTheory.T.lattice_point_count_scaling
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:57.735204+00:00
-- url     : https://prove2.me/theorems/362cc65e-9d27-423f-bf98-cc1de1453726
-- title:
--   T: lattice point count scaling
-- statement:
--   The T construction uses the lattice point count scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScalingStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticePointCountScalingStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScalingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lattice_point_count_scaling : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (Λ : AddSubgroup G) [Countable Λ] (D K₀ : Set G) (R : Finset G) (T : ℝ → G →+ G) (M : ℕ), MeasurableSet D → IsCompact K₀ → D ⊆ K₀ → μ D = 1 → (∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) → (∀ ε : ℝ, 0 < ε → Continuous (T ε)) → (∀ ε : ℝ, 0 < ε → ∀ y, T ε⁻¹ (T ε y) = y ∧ T ε (T ε⁻¹ y) = y) → (∀ ε : ℝ, 0 < ε → Measure.map (T ε) μ = ENNReal.ofReal ((ε ^ M)⁻¹) • μ) → (∀ B : Set G, IsCompact B → ∀ U ∈ 𝓝 (0 : G), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ b ∈ B, T ε b ∈ U) → ∀ (x0 : G) (φ : G → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun l : Λ => φ (T ε (x0 + l))) ∧ Tendsto (fun ε : ℝ => ε ^ M * ∑' l : Λ, φ (T ε (x0 + l))) (𝓝[>] 0) (𝓝 ((R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ)) := by sorry
