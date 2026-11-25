-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_ph_apply
-- name    : GlobalTheory.LevDesc.ph_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:13.455273+00:00
-- url     : https://prove2.me/theorems/f37b8bcf-2af8-4fc6-948f-1066ae15452f
-- title:
--   Lev Desc: ph apply
-- statement:
--   The Lev Desc construction uses the ph apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L109-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L109-L109

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
variable [Fintype G]

theorem GlobalTheory.LevDesc.ph_apply (χ : G →* Kˣ) (u f : R) (h : G) : ph st χ u f h = tr st χ (f * st h u) := by sorry
