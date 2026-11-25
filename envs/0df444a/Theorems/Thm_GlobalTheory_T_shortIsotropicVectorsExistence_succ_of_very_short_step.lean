-- Prove2me | Theorems.Thm_GlobalTheory_T_shortIsotropicVectorsExistence_succ_of_very_short_step
-- name    : GlobalTheory.T.shortIsotropicVectorsExistence_succ_of_very_short_step
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:57:38.890045+00:00
-- url     : https://prove2.me/theorems/fd4fba1c-f482-4ac6-9057-35783bc685f1
-- title:
--   T: short Isotropic Vectors Existence succ of very short step
-- statement:
--   The T construction uses the short Isotropic Vectors Existence succ of very short step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.shortIsotropicVectorsExistence_succ_of_very_short_step : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, (∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ N D 0 C) → (∀ (D : ℕ) (ε : ℝ), 0 < D → 0 < ε → ∃ C : ℝ, ShortIso Ψ (N + 1) D ε C) → ∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ (N + 1) D 0 C := by sorry
