-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_out_mk
-- name    : GroundTheory.Automorphic.Parabolic.apply_out_mk
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:14.138511+00:00
-- url     : https://prove2.me/theorems/3b9f6aee-7fc5-5d3c-a8a4-7053392f717f
-- title:
--   Parabolic: apply out mk
-- statement:
--   The Parabolic construction uses the apply out mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingSums.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingSums.lean#L25-L28

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function
open scoped Pointwise
variable {G : Type*} [Group G] (H : Subgroup G) {M : Type*} [AddCommMonoid M]
variable {H}

theorem GroundTheory.Automorphic.Parabolic.apply_out_mk {X : Type*} {Φ : G → X} (hΦ : ∀ g, ∀ h ∈ H, Φ (g * h) = Φ g) (g : G) :
    Φ (QuotientGroup.mk g : G ⧸ H).out = Φ g := by sorry
