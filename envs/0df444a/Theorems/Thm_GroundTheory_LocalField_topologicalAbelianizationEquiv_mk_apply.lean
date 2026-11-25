-- Prove2me | Theorems.Thm_GroundTheory_LocalField_topologicalAbelianizationEquiv_mk_apply
-- name    : GroundTheory.LocalField.topologicalAbelianizationEquiv_mk_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:54.941352+00:00
-- url     : https://prove2.me/theorems/7412eb38-f6c4-4d78-9357-45d54af339c3
-- title:
--   Local Field: topological Abelianization Equiv mk apply
-- statement:
--   The Local Field construction uses the topological Abelianization Equiv mk apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L50-L53

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
variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
variable [IsGalois F Ω]

theorem GroundTheory.LocalField.topologicalAbelianizationEquiv_mk_apply (σ : Ω ≃ₐ[F] Ω) (x : maximalAbelianExtension F Ω) :
    ((topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) x : _) : Ω) =
      σ x := by sorry
