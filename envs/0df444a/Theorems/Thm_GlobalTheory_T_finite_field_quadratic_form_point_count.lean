-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_field_quadratic_form_point_count
-- name    : GlobalTheory.T.finite_field_quadratic_form_point_count
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:38:55.166264+00:00
-- url     : https://prove2.me/theorems/1592f654-ad46-4403-98da-654a58c3b019
-- title:
--   T: finite field quadratic form point count
-- statement:
--   The T construction uses the finite field quadratic form point count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCountStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCountStatement.lean#L8-L9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCountStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_field_quadratic_form_point_count : ∀ (k : Type) [Field k] [Fintype k], ringChar k ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 1 ≤ M → ∀ (B : Matrix ι ι k), B.IsSymm → B.det ≠ 0 → ∀ s : k, |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M := by sorry
