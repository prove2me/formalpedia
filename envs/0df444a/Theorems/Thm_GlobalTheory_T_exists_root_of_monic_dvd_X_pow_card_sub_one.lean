-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_root_of_monic_dvd_X_pow_card_sub_one
-- name    : GlobalTheory.T.exists_root_of_monic_dvd_X_pow_card_sub_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:30:15.07549+00:00
-- url     : https://prove2.me/theorems/623bd96a-4e00-47f9-9e0e-88ce223a171b
-- title:
--   T: exists root of monic dvd X pow card sub one
-- statement:
--   The T construction uses the exists root of monic dvd X pow card sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MonicDvdXPowCardSubOneExistsRootStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MonicDvdXPowCardSubOneExistsRootStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MonicDvdXPowCardSubOneExistsRoot
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MonicDvdXPowCardSubOneExistsRootStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_root_of_monic_dvd_X_pow_card_sub_one : ∀ (S : Type) [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)] (f : S[X]), f.Monic → f.natDegree ≠ 0 → f ∣ X ^ (Nat.card (ResidueField S) - 1) - 1 → ∃ y : S, f.eval y = 0 := by sorry
