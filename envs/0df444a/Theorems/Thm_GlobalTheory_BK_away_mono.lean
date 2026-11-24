-- Prove2me | Theorems.Thm_GlobalTheory_BK_away_mono
-- name    : GlobalTheory.BK.away_mono
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:11.226133+00:00
-- url     : https://prove2.me/theorems/4110bab3-5243-4578-b2f1-39ec03fde7b6
-- title:
--   BK: away mono
-- statement:
--   The BK construction uses the away mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L263-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L263-L264

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

theorem GlobalTheory.BK.away_mono {B B' : Subalgebra O K⟦X⟧} (h : B ≤ B') {s : B} {s' : B'}
    (hs : (s : K⟦X⟧) = s') : away B s ≤ away B' s' := by sorry
