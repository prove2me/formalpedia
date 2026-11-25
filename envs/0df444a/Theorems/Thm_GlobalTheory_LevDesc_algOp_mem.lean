-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_algOp_mem
-- name    : GlobalTheory.LevDesc.algOp_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:12:58.367275+00:00
-- url     : https://prove2.me/theorems/9facedec-42a3-5d3a-8db0-61f3b3277bfa
-- title:
--   Lev Desc: alg Op mem
-- statement:
--   The Lev Desc construction uses the alg Op mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L94-L97

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

theorem GlobalTheory.LevDesc.algOp_mem {C : Submodule K R} (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) (e : MonoidAlgebra K G) {x : R} (hx : x ∈ C) :
    algOp st e x ∈ C := by sorry
