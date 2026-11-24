-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_IsRightAct_leftRep_apply
-- name    : GlobalTheory.LevDesc.IsRightAct.leftRep_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:02:15.37934+00:00
-- url     : https://prove2.me/theorems/7b7b8057-263a-49bb-98e1-4a7d8cd68cec
-- title:
--   Is Right Act: left Rep apply
-- statement:
--   The Is Right Act construction uses the left Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L56-L57

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
variable (st : G → R →ₐ[K] R)

theorem GlobalTheory.LevDesc.IsRightAct.leftRep_apply {st : G → R →ₐ[K] R} (hs : IsRightAct st) (g : G) (x : R) :
    hs.leftRep g x = st g⁻¹ x := by sorry
