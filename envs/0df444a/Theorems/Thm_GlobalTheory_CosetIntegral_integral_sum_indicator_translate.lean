-- Prove2me | Theorems.Thm_GlobalTheory_CosetIntegral_integral_sum_indicator_translate
-- name    : GlobalTheory.CosetIntegral.integral_sum_indicator_translate
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:27:12.895824+00:00
-- url     : https://prove2.me/theorems/641ae213-b319-4bbc-a98f-a9fb1a0001cd
-- title:
--   Coset Integral: integral sum indicator translate
-- statement:
--   The Coset Integral construction uses the integral sum indicator translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralSumIndicatorTranslate.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralSumIndicatorTranslate.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralSumIndicatorTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CosetIntegral

theorem GlobalTheory.CosetIntegral.integral_sum_indicator_translate {G ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (m : Measure G)
    [m.IsMulRightInvariant] (H : Set G) (hH : IsOpen H) (hm : m H = 1) (T : Finset ι)
    (r : ι → G) (c : ι → ℂ) :
    ∫ x, ∑ q ∈ T, ((fun y => y * (r q)⁻¹) ⁻¹' H).indicator (fun _ => c q) x ∂m
      = ∑ q ∈ T, c q := by sorry
