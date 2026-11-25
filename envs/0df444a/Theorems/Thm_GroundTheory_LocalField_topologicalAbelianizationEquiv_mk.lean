-- Prove2me | Theorems.Thm_GroundTheory_LocalField_topologicalAbelianizationEquiv_mk
-- name    : GroundTheory.LocalField.topologicalAbelianizationEquiv_mk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:49.969303+00:00
-- url     : https://prove2.me/theorems/68d85340-dd58-48d2-ae2e-55f227a67ff6
-- title:
--   Local Field: topological Abelianization Equiv mk
-- statement:
--   The Local Field construction uses the topological Abelianization Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L45-L48

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

theorem GroundTheory.LocalField.topologicalAbelianizationEquiv_mk (σ : Ω ≃ₐ[F] Ω) :
    topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) =
      AlgEquiv.restrictNormalHom (maximalAbelianExtension F Ω) σ := by sorry
