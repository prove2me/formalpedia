-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_algEquiv_apply_eq_of_transcendental
-- name    : GroundTheory.Global.exists_algEquiv_apply_eq_of_transcendental
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:38.48081+00:00
-- url     : https://prove2.me/theorems/b85022cf-3d76-4cf1-9c2d-cea2b3433cac
-- title:
--   Global: exists alg Equiv apply eq of transcendental
-- statement:
--   The Global construction uses the exists alg Equiv apply eq of transcendental property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L22-L38

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

theorem GroundTheory.Global.exists_algEquiv_apply_eq_of_transcendental {x y : Ω} (hx : Transcendental F x)
    (hy : Transcendental F y) : ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by sorry
