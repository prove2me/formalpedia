-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_IsPart_unique
-- name    : GlobalTheory.HeckeTate.IsPart.unique
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:51.427839+00:00
-- url     : https://prove2.me/theorems/c86dab53-4cf4-449d-bc41-c70bad2b57d0
-- title:
--   Is Part: unique
-- statement:
--   The Is Part construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L38-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R]

theorem GlobalTheory.HeckeTate.IsPart.unique {P : Ideal R} {N e e' : R} (h : IsPart P N e) (h' : IsPart P N e') :
    N ∣ e - e' := by sorry
