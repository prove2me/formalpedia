-- Prove2me | Theorems.Thm_GlobalTheory_MonoDeg_card_eq_card_finsuppAntidiag
-- name    : GlobalTheory.MonoDeg.card_eq_card_finsuppAntidiag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:12.919809+00:00
-- url     : https://prove2.me/theorems/eb1fd6a5-9fb6-4569-b811-510ebe21fcba
-- title:
--   Mono Deg: card eq card finsupp Antidiag
-- statement:
--   The Mono Deg construction uses the card eq card finsupp Antidiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L24-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.MonoDeg.card_eq_card_finsuppAntidiag (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ℕ) :
    Fintype.card (MonoDeg ι a) = (Finset.finsuppAntidiag (Finset.univ : Finset ι) a).card := by sorry
