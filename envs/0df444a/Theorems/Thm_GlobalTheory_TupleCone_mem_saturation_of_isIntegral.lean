-- Prove2me | Theorems.Thm_GlobalTheory_TupleCone_mem_saturation_of_isIntegral
-- name    : GlobalTheory.TupleCone.mem_saturation_of_isIntegral
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:31.213908+00:00
-- url     : https://prove2.me/theorems/3aa44124-1467-5186-bf23-5934b66cb722
-- title:
--   Tuple Cone: mem saturation of is Integral
-- statement:
--   The Tuple Cone construction uses the mem saturation of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L34-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L34-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem GlobalTheory.TupleCone.mem_saturation_of_isIntegral {x : B} (hx : IsIntegral A x) {b : B}
    (hb : IsIntegral (saturation x hx) b) : b ∈ saturation x hx := by sorry
