-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_IsPart_of_dvd
-- name    : GlobalTheory.HeckeTate.IsPart.of_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:26.304655+00:00
-- url     : https://prove2.me/theorems/25a4d7b9-f495-47d7-a48b-6e7fb6e54c92
-- title:
--   Is Part: of dvd
-- statement:
--   The Is Part construction uses the of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L35-L36

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

theorem GlobalTheory.HeckeTate.IsPart.of_dvd {P : Ideal R} {N N' e : R} (h : IsPart P N' e) (hN : N ∣ N') : IsPart P N e := by sorry
