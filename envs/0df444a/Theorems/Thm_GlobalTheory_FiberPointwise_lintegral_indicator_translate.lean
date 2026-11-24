-- Prove2me | Theorems.Thm_GlobalTheory_FiberPointwise_lintegral_indicator_translate
-- name    : GlobalTheory.FiberPointwise.lintegral_indicator_translate
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:23:12.939495+00:00
-- url     : https://prove2.me/theorems/da6d2cbc-2e1f-4993-a082-3c8791c498ad
-- title:
--   Fiber Pointwise: lintegral indicator translate
-- statement:
--   The Fiber Pointwise construction uses the lintegral indicator translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingOfProjectionSupport.lean#L6-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingOfProjectionSupport.lean#L6-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingOfProjectionSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.FiberPointwise

theorem GlobalTheory.FiberPointwise.lintegral_indicator_translate {X : Type} [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd X]
    (μ : Measure X) [μ.IsAddRightInvariant] (P : X →+ X)
    (h : X → ENNReal) (hinv : ∀ x z, P z = z → h (x + z) = h x) (S : Set X) (z : X) (hz : P z = z) :
    ∫⁻ x, Set.indicator {x | P x - z ∈ S} h x ∂μ = ∫⁻ x, Set.indicator {x | P x ∈ S} h x ∂μ := by sorry
