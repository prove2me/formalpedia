-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_IsRightAct_tr_mem_eigen
-- name    : GlobalTheory.LevDesc.IsRightAct.tr_mem_eigen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:06.66803+00:00
-- url     : https://prove2.me/theorems/8f472e45-3673-417d-bb37-55596c4a838d
-- title:
--   Is Right Act: tr mem eigen
-- statement:
--   The Is Right Act construction uses the tr mem eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L116-L122

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

theorem GlobalTheory.LevDesc.IsRightAct.tr_mem_eigen {st : G → R →ₐ[K] R} (hs : IsRightAct st) (χ : G →* Kˣ) (F : R) :
    tr st χ F ∈ eigen st χ := by sorry
