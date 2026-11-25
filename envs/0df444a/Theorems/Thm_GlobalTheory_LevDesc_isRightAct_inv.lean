-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_isRightAct_inv
-- name    : GlobalTheory.LevDesc.isRightAct_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:04.023948+00:00
-- url     : https://prove2.me/theorems/272f63fd-b92d-563c-94e0-599f7b8953dc
-- title:
--   Lev Desc: is Right Act inv
-- statement:
--   The Lev Desc construction uses the is Right Act inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L16-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
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
open GlobalTheory GlobalTheory.LevDesc
variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]

theorem GlobalTheory.LevDesc.isRightAct_inv (ρ : G →* (R →ₐ[K] R)) : IsRightAct (fun h => ρ h⁻¹) := by sorry
