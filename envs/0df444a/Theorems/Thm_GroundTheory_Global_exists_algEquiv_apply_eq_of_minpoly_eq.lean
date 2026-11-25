-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_algEquiv_apply_eq_of_minpoly_eq
-- name    : GroundTheory.Global.exists_algEquiv_apply_eq_of_minpoly_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:28.27756+00:00
-- url     : https://prove2.me/theorems/c4807a4c-98e8-4524-a379-350bec71a42a
-- title:
--   Global: exists alg Equiv apply eq of minpoly eq
-- statement:
--   The Global construction uses the exists alg Equiv apply eq of minpoly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L40-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L40-L56

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

theorem GroundTheory.Global.exists_algEquiv_apply_eq_of_minpoly_eq {x y : Ω} (hx : IsAlgebraic F x)
    (h : minpoly F x = minpoly F y) : ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by sorry
