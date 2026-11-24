-- Prove2me | Theorems.Thm_GlobalTheory_T_denominator_power_summable
-- name    : GlobalTheory.T.denominator_power_summable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:48:12.531299+00:00
-- url     : https://prove2.me/theorems/ba4decea-512d-48f2-a6b8-28f712181e71
-- title:
--   T: denominator power summable
-- statement:
--   The T construction uses the denominator power summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DenominatorPowerSummableStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DenominatorPowerSummableStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummable
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummableStatement
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

theorem GlobalTheory.T.denominator_power_summable : ∀ (F : Type) [Field F] [NumberField F], ∀ M : ℕ, 3 ≤ M → ∀ N : ℕ, 0 < N → (∀ (b : F) (r : 𝓞 F), den (b + (r : F)) = den b) ∧ (∀ b : F, 0 < den b) ∧ ∀ s : Set F, (∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b') → Summable fun b : s => ((den (b : F) : ℝ) ^ M)⁻¹ := by sorry
