-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_quadric_count_even
-- name    : GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:07:38.050146+00:00
-- url     : https://prove2.me/theorems/f96d9147-fff4-4320-b0b0-ea81d1bd9adc
-- title:
--   Quadric Count: quadric count even
-- statement:
--   The Quadric Count construction uses the quadric count even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCount.lean#L163-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCount.lean#L163-L164

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricCount
open ComplexConjugate
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even : ∀ (k : Type) [Field k] [Fintype k], ringChar k ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 1 ≤ M → ∀ (B : Matrix ι ι k), B.IsSymm → B.det ≠ 0 → ∀ s : k, |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M := by sorry
