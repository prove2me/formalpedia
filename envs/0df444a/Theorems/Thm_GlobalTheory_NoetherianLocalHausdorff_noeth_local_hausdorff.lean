-- Prove2me | Theorems.Thm_GlobalTheory_NoetherianLocalHausdorff_noeth_local_hausdorff
-- name    : GlobalTheory.NoetherianLocalHausdorff.noeth_local_hausdorff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:34:44.661361+00:00
-- url     : https://prove2.me/theorems/dd863384-51af-45f6-a656-54d364429706
-- title:
--   Noetherian Local Hausdorff: noeth local hausdorff
-- statement:
--   The Noetherian Local Hausdorff construction uses the noeth local hausdorff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NoethLocalHausdorff.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NoethLocalHausdorff.lean#L5-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NoethLocalHausdorff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherianLocalHausdorff

theorem GlobalTheory.NoetherianLocalHausdorff.noeth_local_hausdorff : ∀ (B : Type) [inst : CommRing B] [inst_1 : IsLocalRing B] [IsNoetherianRing B],
    IsHausdorff (IsLocalRing.maximalIdeal B) B := by sorry
