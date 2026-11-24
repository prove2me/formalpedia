-- Prove2me | Theorems.Thm_GlobalTheory_SW_shortIso_step
-- name    : GlobalTheory.SW.shortIso_step
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:48.475418+00:00
-- url     : https://prove2.me/theorems/cd325904-3de8-4ef4-911b-05188b9aae24
-- title:
--   SW: short Iso step
-- statement:
--   The SW construction uses the short Iso step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L410-L533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L410-L533

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
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
open GlobalTheory.SW.MinkowskiProductBounds GlobalTheory.SW.ShortStep

theorem GlobalTheory.SW.shortIso_step : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, (∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ N D 0 C) → (∀ (D : ℕ) (ε : ℝ), 0 < D → 0 < ε → ∃ C : ℝ, ShortIso Ψ (N + 1) D ε C) → ∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ (N + 1) D 0 C := by sorry
