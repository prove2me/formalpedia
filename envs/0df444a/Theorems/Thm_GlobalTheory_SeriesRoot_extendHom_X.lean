-- Prove2me | Theorems.Thm_GlobalTheory_SeriesRoot_extendHom_X
-- name    : GlobalTheory.SeriesRoot.extendHom_X
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:35.30095+00:00
-- url     : https://prove2.me/theorems/a42ce56b-37f0-41be-a440-cdc30f998b10
-- title:
--   Series Root: extend Hom X
-- statement:
--   The Series Root construction uses the extend Hom X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRingHomPowerSeriesRoot.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRingHomPowerSeriesRoot.lean#L113-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingHomPowerSeriesRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory
open GlobalTheory.SeriesRoot
variable {O : Type*} [CommRing O]
variable {K : Type*} [CommRing K]

theorem GlobalTheory.SeriesRoot.extendHom_X (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) : extendHom φ hk ht X = t := by sorry
