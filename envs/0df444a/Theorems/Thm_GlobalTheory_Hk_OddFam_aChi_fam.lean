-- Prove2me | Theorems.Thm_GlobalTheory_Hk_OddFam_aChi_fam
-- name    : GlobalTheory.Hk.OddFam.aChi_fam
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:46.080322+00:00
-- url     : https://prove2.me/theorems/b5a55d61-85ea-43dc-bb1d-8031daae26af
-- title:
--   Odd Fam: a Chi fam
-- statement:
--   The Odd Fam construction uses the a Chi fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L257-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L257-L260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Hk
attribute [instance] LFam.ag LFam.ft
open GlobalTheory.Hk.OddFam

theorem GlobalTheory.Hk.OddFam.aChi_fam (n : ℕ) : fam.aChi 1 n = if Odd n then 1 else 0 := by sorry
