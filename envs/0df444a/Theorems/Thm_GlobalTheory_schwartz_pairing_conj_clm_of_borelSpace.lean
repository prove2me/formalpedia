-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_pairing_conj_clm_of_borelSpace
-- name    : GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:51.561317+00:00
-- url     : https://prove2.me/theorems/10051b73-66f8-4367-9a85-c21d2324ea7d
-- title:
--   Global Theory: schwartz pairing conj clm of borel Space
-- statement:
--   The Global Theory construction uses the schwartz pairing conj clm of borel Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzPairingContinuousFunctional.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzPairingContinuousFunctional.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzPairingContinuousFunctional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap
open GlobalTheory

theorem GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (k : SchwartzMap V ℂ) :
    ∃ L : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      L u = ∫ x, u x * starRingEnd ℂ (k x) ∂μ := by sorry
