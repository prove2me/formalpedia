-- Prove2me | Theorems.Thm_GlobalTheory_monic_dvd_X_pow_card_sub_one_exists_root
-- name    : GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:10:56.018326+00:00
-- url     : https://prove2.me/theorems/94a31e53-9034-4736-a58b-250a26ccb1f0
-- title:
--   Global Theory: monic dvd X pow card sub one exists root
-- statement:
--   The Global Theory construction uses the monic dvd X pow card sub one exists root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MonicDvdXPowCardSubOneExistsRoot.lean#L6-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MonicDvdXPowCardSubOneExistsRoot.lean#L6-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MonicDvdXPowCardSubOneExistsRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
open GlobalTheory

theorem GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root :
    ∀ (S : Type) [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)] (f : S[X]),
      f.Monic → f.natDegree ≠ 0 → f ∣ X ^ (Nat.card (ResidueField S) - 1) - 1 →
        ∃ y : S, f.eval y = 0 := by sorry
