-- Prove2me | Theorems.Thm_GlobalTheory_localizedModule_mk_quotient_eq_zero_iff_dvd
-- name    : GlobalTheory.localizedModule_mk_quotient_eq_zero_iff_dvd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:08:03.768799+00:00
-- url     : https://prove2.me/theorems/95b9bf49-62c3-4ffb-8622-5303508491ef
-- title:
--   Global Theory: localized Module mk quotient eq zero iff dvd
-- statement:
--   The Global Theory construction uses the localized Module mk quotient eq zero iff dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinitePrimesDvdOfDvdMulLocalization.lean#L5-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinitePrimesDvdOfDvdMulLocalization.lean#L5-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePrimesDvdOfDvdMulLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.localizedModule_mk_quotient_eq_zero_iff_dvd {R : Type} [CommRing R] (M : Submonoid R)
    (s c : R) :
    LocalizedModule.mkLinearMap M (R ⧸ Ideal.span {s}) (Ideal.Quotient.mk _ c) = 0 ↔
      algebraMap R (Localization M) s ∣ algebraMap R (Localization M) c := by sorry
