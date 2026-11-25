-- Prove2me | Theorems.Thm_GroundTheory_Global_trdeg_eq_cardinalMk_of_countable
-- name    : GroundTheory.Global.trdeg_eq_cardinalMk_of_countable
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:47.746989+00:00
-- url     : https://prove2.me/theorems/bb1f01bf-c134-49fd-a501-a70cee642917
-- title:
--   Global: trdeg eq cardinal Mk of countable
-- statement:
--   The Global construction uses the trdeg eq cardinal Mk of countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ExistsRingEquivExtendOfIsTranscendenceBasis.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ExistsRingEquivExtendOfIsTranscendenceBasis.lean#L44-L49

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
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
open Cardinal Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]

theorem GroundTheory.Global.trdeg_eq_cardinalMk_of_countable (F : Type*) [Field F] [Algebra F Ω] [Countable F]
    (hΩ : ℵ₀ < #Ω) : Algebra.trdeg F Ω = #Ω := by sorry
