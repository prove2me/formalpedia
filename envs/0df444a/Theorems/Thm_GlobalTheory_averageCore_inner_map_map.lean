-- Prove2me | Theorems.Thm_GlobalTheory_averageCore_inner_map_map
-- name    : GlobalTheory.averageCore_inner_map_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:56.233292+00:00
-- url     : https://prove2.me/theorems/b15dbce1-e6ac-452a-adfd-b9e1ba9c3f5c
-- title:
--   Global Theory: average Core inner map map
-- statement:
--   The Global Theory construction uses the average Core inner map map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L295-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L295-L302

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

theorem GlobalTheory.averageCore_inner_map_map [MeasurableSpace K] [BorelSpace K] {V E : Type*}
    [AddCommGroup V] [Module 𝕜 V] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (ρ : Representation 𝕜 K V) (e : V →ₗ[𝕜] E) (he : Function.Injective e)
    (hc : ∀ v, Continuous fun k => e (ρ k v)) (g : K) (u v : V) :
    (averageCore ρ e he hc).inner (ρ g u) (ρ g v) = (averageCore ρ e he hc).inner u v := by sorry
