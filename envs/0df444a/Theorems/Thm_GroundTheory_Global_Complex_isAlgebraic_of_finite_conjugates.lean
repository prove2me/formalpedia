-- Prove2me | Theorems.Thm_GroundTheory_Global_Complex_isAlgebraic_of_finite_conjugates
-- name    : GroundTheory.Global.Complex.isAlgebraic_of_finite_conjugates
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:12.203215+00:00
-- url     : https://prove2.me/theorems/a03cb8db-658c-560b-b984-34c9adff5b47
-- title:
--   Complex: is Algebraic of finite conjugates
-- statement:
--   The Complex construction uses the is Algebraic of finite conjugates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L118-L120

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

theorem GroundTheory.Global.Complex.isAlgebraic_of_finite_conjugates {x : ℂ}
    (hx : (Set.range fun σ : ℂ ≃+* ℂ => σ x).Finite) : IsAlgebraic ℚ x := by sorry
