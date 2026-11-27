-- Prove2me | Theorems.Thm_GlobalTheory_dvd_of_smul_apply_eq_smul
-- name    : GlobalTheory.dvd_of_smul_apply_eq_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:55.395454+00:00
-- url     : https://prove2.me/theorems/7de85035-2756-485b-8fa3-e4c85f10e9d8
-- title:
--   Global Theory: dvd of smul apply eq smul
-- statement:
--   The Global Theory construction uses the dvd of smul apply eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GroupLikeIntegralOfFiniteFree.lean#L6-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GroupLikeIntegralOfFiniteFree.lean#L6-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GroupLikeIntegralOfFiniteFree
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

theorem GlobalTheory.dvd_of_smul_apply_eq_smul (O C A : Type) [CommRing O] [IsDomain O] [Field C] [Algebra O C]
    [IsFractionRing O C] [IsIntegrallyClosed O] [AddCommGroup A] [Module O A] [Module.Finite O A]
    (T : Module.End O A) (ε : A →ₗ[O] O) (d c : O) (a : A) (hd : d ≠ 0) (hε : ε a ≠ 0)
    (h : d • T a = c • a) : d ∣ c := by sorry
