-- Prove2me | Theorems.Thm_GlobalTheory_RealZeros_strictAntiOn_diff
-- name    : GlobalTheory.RealZeros.strictAntiOn_diff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:17:55.7137+00:00
-- url     : https://prove2.me/theorems/4c54172d-8997-4267-b68f-1ffcb871b484
-- title:
--   Real Zeros: strict Anti On diff
-- statement:
--   The Real Zeros construction uses the strict Anti On diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L165-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean#L165-L178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros

theorem GlobalTheory.RealZeros.strictAntiOn_diff {σ : ℝ} (h0 : 0 < σ) :
    StrictAntiOn (fun x : ℝ => x ^ (-σ) - (x + 2) ^ (-σ)) (Set.Ioi 0) := by sorry
