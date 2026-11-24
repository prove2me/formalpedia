-- Prove2me | Theorems.Thm_GroundTheory_Global_IsTranscendenceBasis_extendScalars_of_isAlgebraic
-- name    : GroundTheory.Global.IsTranscendenceBasis.extendScalars_of_isAlgebraic
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:30.823807+00:00
-- url     : https://prove2.me/theorems/5d9441a2-0b45-40b0-84ec-ef21aee49206
-- title:
--   Is Transcendence Basis: extend Scalars of is Algebraic
-- statement:
--   The Is Transcendence Basis construction uses the extend Scalars of is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean#L14-L20

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
omit [IsAlgClosed Ω]

theorem GroundTheory.Global.IsTranscendenceBasis.extendScalars_of_isAlgebraic {E : Type*} [Field E] [Algebra F E]
    [Algebra E Ω] [IsScalarTower F E Ω] [Algebra.IsAlgebraic F E] {ι : Type*} {v : ι → Ω}
    (hv : IsTranscendenceBasis F v) : IsTranscendenceBasis E v := by sorry
