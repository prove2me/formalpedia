-- Prove2me | Theorems.Thm_GroundTheory_Global_infinite_range_apply_of_transcendental
-- name    : GroundTheory.Global.infinite_range_apply_of_transcendental
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:29.708921+00:00
-- url     : https://prove2.me/theorems/5230052d-4e7e-4a0b-a48c-dc4c7031d593
-- title:
--   Global: infinite range apply of transcendental
-- statement:
--   The Global construction uses the infinite range apply of transcendental property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L82-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L82-L97

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
variable [CharZero Ω]

theorem GroundTheory.Global.infinite_range_apply_of_transcendental {x : Ω} (hx : Transcendental ℚ x) :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Infinite := by sorry
