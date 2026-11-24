-- Prove2me | Theorems.Thm_GroundTheory_Global_finite_range_apply_iff_isAlgebraic
-- name    : GroundTheory.Global.finite_range_apply_iff_isAlgebraic
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:14.781615+00:00
-- url     : https://prove2.me/theorems/9c1e4e44-7983-4b85-b56f-b4879c25b9e0
-- title:
--   Global: finite range apply iff is Algebraic
-- statement:
--   The Global construction uses the finite range apply iff is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L111-L114

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

theorem GroundTheory.Global.finite_range_apply_iff_isAlgebraic {x : Ω} :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Finite ↔ IsAlgebraic ℚ x := by sorry
