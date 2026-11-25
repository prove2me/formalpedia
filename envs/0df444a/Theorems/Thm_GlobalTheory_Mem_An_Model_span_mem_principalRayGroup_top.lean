-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_Model_span_mem_principalRayGroup_top
-- name    : GlobalTheory.Mem.An.Model.span_mem_principalRayGroup_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:13.21185+00:00
-- url     : https://prove2.me/theorems/d497256f-1dc6-4c50-9f62-3f0fd6674bec
-- title:
--   Model: span mem principal Ray Group top
-- statement:
--   The Model construction uses the span mem principal Ray Group top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L35-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model

theorem GlobalTheory.Mem.An.Model.span_mem_principalRayGroup_top {K : Type} [Field K] [NumberField K] (a : 𝓞 K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : (I : FractionalIdeal (𝓞 K)⁰ K) = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    I ∈ rayP (⊤ : Ideal (𝓞 K)) := by sorry
