-- Prove2me | Theorems.Thm_GlobalTheory_BK_frob_injective
-- name    : GlobalTheory.BK.frob_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:41.410213+00:00
-- url     : https://prove2.me/theorems/11eaeccc-b2be-4e95-bc39-949ea1ceb4e5
-- title:
--   BK: frob injective
-- statement:
--   The BK construction uses the frob injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L292-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L292-L295

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
omit [IsUltrametricDist K] [IsUnitBall O K]

theorem GlobalTheory.BK.frob_injective (l : ℕ) [Fact l.Prime] : Function.Injective (frob K l) := by sorry
