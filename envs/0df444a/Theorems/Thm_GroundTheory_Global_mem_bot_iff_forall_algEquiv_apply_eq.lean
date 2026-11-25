-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_bot_iff_forall_algEquiv_apply_eq
-- name    : GroundTheory.Global.mem_bot_iff_forall_algEquiv_apply_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:56:08.080185+00:00
-- url     : https://prove2.me/theorems/c5074c3f-7023-4780-b52e-f01f6922ef64
-- title:
--   Global: mem bot iff forall alg Equiv apply eq
-- statement:
--   The Global construction uses the mem bot iff forall alg Equiv apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L58-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L58-L78

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AutCFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {F : Type*} [Field F] [Algebra F Ω]

theorem GroundTheory.Global.mem_bot_iff_forall_algEquiv_apply_eq [PerfectField F] {x : Ω} :
    x ∈ (⊥ : IntermediateField F Ω) ↔ ∀ σ : Ω ≃ₐ[F] Ω, σ x = x := by sorry
