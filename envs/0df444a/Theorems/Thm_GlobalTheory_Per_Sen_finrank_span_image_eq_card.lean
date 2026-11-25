-- Prove2me | Theorems.Thm_GlobalTheory_Per_Sen_finrank_span_image_eq_card
-- name    : GlobalTheory.Per.Sen.finrank_span_image_eq_card
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:32.301869+00:00
-- url     : https://prove2.me/theorems/603b5486-0abc-413e-b2a3-0ae10ca45bed
-- title:
--   Sen: finrank span image eq card
-- statement:
--   The Sen construction uses the finrank span image eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankSpanImageEqCard.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankSpanImageEqCard.lean#L8-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AntitoneFiltrationExistsAdaptedLinearIndepSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankSpanImageEqCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.Per GlobalTheory.Per.Sen

theorem GlobalTheory.Per.Sen.finrank_span_image_eq_card {L M : Type} [Field L] [AddCommGroup M] [Module L M] {m : ℕ}
    (d : Fin m → M) (hd : LinearIndependent L d) (p : Fin m → Prop) [DecidablePred p] :
    Module.finrank L (Submodule.span L (d '' {i | p i})) = (Finset.univ.filter p).card := by sorry
