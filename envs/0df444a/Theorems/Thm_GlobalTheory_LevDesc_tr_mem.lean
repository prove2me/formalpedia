-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_tr_mem
-- name    : GlobalTheory.LevDesc.tr_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:15.576929+00:00
-- url     : https://prove2.me/theorems/032e6df5-960e-556a-b273-301429d93c67
-- title:
--   Lev Desc: tr mem
-- statement:
--   The Lev Desc construction uses the tr mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L128-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L128-L130

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

theorem GlobalTheory.LevDesc.tr_mem {C : Submodule K R} (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) (χ : G →* Kˣ) {x : R} (hx : x ∈ C) :
    tr st χ x ∈ C := by sorry
