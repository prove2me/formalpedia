-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_IsRightAct_subRep_apply
-- name    : GlobalTheory.LevDesc.IsRightAct.subRep_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:31.64261+00:00
-- url     : https://prove2.me/theorems/7cfa4326-d103-4f29-a1fe-80bb8d4b4ea3
-- title:
--   Is Right Act: sub Rep apply
-- statement:
--   The Is Right Act construction uses the sub Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L68-L69

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

theorem GlobalTheory.LevDesc.IsRightAct.subRep_apply {st : G → R →ₐ[K] R} (hs : IsRightAct st) (C : Submodule K R)
    (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) (g : G) (x : C) : (hs.subRep C hC g x : R) = st g⁻¹ x := by sorry
