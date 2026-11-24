-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ext_restrictAb
-- name    : GroundTheory.LocalField.ext_restrictAb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:39.902939+00:00
-- url     : https://prove2.me/theorems/abf7109c-dfea-4229-b360-5cd35bc71e2e
-- title:
--   Local Field: ext restrict Ab
-- statement:
--   The Local Field construction uses the ext restrict Ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L165-L172

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open IntermediateField
open scoped commutatorElement
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem GroundTheory.LocalField.ext_restrictAb {σ τ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω}
    (h : ∀ (L : IntermediateField F Ω) [FiniteDimensional F L] [IsAbelianGalois F L],
      restrictAb L (le_maximalAbelianExtension L) σ = restrictAb L (le_maximalAbelianExtension L) τ) :
    σ = τ := by sorry
