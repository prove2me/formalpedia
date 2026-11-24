-- Prove2me | Theorems.Thm_GlobalTheory_FlagVolume_lintegral_radial
-- name    : GlobalTheory.FlagVolume.lintegral_radial
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:55.063659+00:00
-- url     : https://prove2.me/theorems/fcac646d-c1ad-4b04-8480-56811ea2b1a5
-- title:
--   Flag Volume: lintegral radial
-- statement:
--   The Flag Volume construction uses the lintegral radial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralProdPartialSums.lean#L8-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralProdPartialSums.lean#L8-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralProdPartialSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Set Filter Topology
open scoped ENNReal Nat
open GlobalTheory GlobalTheory.FlagVolume

theorem GlobalTheory.FlagVolume.lintegral_radial {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((A + r ^ 2) ^ (m + 2))⁻¹) =
      ENNReal.ofReal ((2 * (m + 1) * A ^ (m + 1))⁻¹) := by sorry
