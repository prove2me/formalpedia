-- Prove2me | Theorems.Thm_GroundTheory_Global_finite_range_apply_of_isAlgebraic
-- name    : GroundTheory.Global.finite_range_apply_of_isAlgebraic
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:15.835053+00:00
-- url     : https://prove2.me/theorems/39ec3b28-f0e5-4d0f-a0fd-91d58f104db3
-- title:
--   Global: finite range apply of is Algebraic
-- statement:
--   The Global construction uses the finite range apply of is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L101-L109

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
omit [IsAlgClosed Ω]

theorem GroundTheory.Global.finite_range_apply_of_isAlgebraic {x : Ω} (hx : IsAlgebraic ℚ x) :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Finite := by sorry
