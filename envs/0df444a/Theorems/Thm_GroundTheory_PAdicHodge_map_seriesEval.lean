-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_map_seriesEval
-- name    : GroundTheory.PAdicHodge.map_seriesEval
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:17.585909+00:00
-- url     : https://prove2.me/theorems/18155c60-2b87-4452-8007-4bd5ad01cbc0
-- title:
--   PAdic Hodge: map series Eval
-- statement:
--   The PAdic Hodge construction uses the map series Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L180-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L180-L192

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
variable {B : Type*} [CommRing B] (I : Ideal B)
variable [Algebra ℚ B]
variable [IsAdicComplete I B]
variable {I}

theorem GroundTheory.PAdicHodge.map_seriesEval {B' : Type*} [CommRing B'] [Algebra ℚ B'] {I' : Ideal B'}
    [IsAdicComplete I' B'] (F : B →+* B') (hF : I.map F ≤ I') {z : B} (hz : z ∈ I)
    (hFz : F z ∈ I') (f : ℚ⟦X⟧) : F (seriesEval I z hz f) = seriesEval I' (F z) hFz f := by sorry
