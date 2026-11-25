-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_sgn_smul
-- name    : GlobalTheory.CechDR.sgn_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:37.548475+00:00
-- url     : https://prove2.me/theorems/35e1d5ed-0437-45fa-92e1-7174de199926
-- title:
--   Cech DR: sgn smul
-- statement:
--   The Cech DR construction uses the sgn smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneFormMapEqKaehlerDifferentialMap.lean#L30-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
variable {R B}

theorem GlobalTheory.CechDR.sgn_smul (r : R) (x : DR R B) : sgn (r • x) = r • sgn x := by sorry
