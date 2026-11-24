-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_exists_isPart
-- name    : GlobalTheory.HeckeTate.exists_isPart
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:05.270111+00:00
-- url     : https://prove2.me/theorems/49929911-b947-491f-967a-1c108a7f4f4e
-- title:
--   Hecke Tate: exists is Part
-- statement:
--   The Hecke Tate construction uses the exists is Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L66-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L66-L85

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

theorem GlobalTheory.HeckeTate.exists_isPart [IsDedekindDomain R] {P : Ideal R} (hP : P.IsMaximal) {N : R} (hN : N ≠ 0) :
    ∃ e, IsPart P N e := by sorry
