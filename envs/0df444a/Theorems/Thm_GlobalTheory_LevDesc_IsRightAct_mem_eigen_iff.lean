-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_IsRightAct_mem_eigen_iff
-- name    : GlobalTheory.LevDesc.IsRightAct.mem_eigen_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:43.113501+00:00
-- url     : https://prove2.me/theorems/29d94a34-63ab-49ec-b63c-17469bdf40ef
-- title:
--   Is Right Act: mem eigen iff
-- statement:
--   The Is Right Act construction uses the mem eigen iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L59-L62

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

theorem GlobalTheory.LevDesc.IsRightAct.mem_eigen_iff {st : G → R →ₐ[K] R} (hs : IsRightAct st) {χ : G →* Kˣ} {F : R} :
    F ∈ eigen st χ ↔ ∀ g, hs.leftRep g F = ((χ⁻¹ g : Kˣ) : K) • F := by sorry
