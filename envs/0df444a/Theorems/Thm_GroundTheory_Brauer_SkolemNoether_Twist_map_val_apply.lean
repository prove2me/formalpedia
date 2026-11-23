-- Prove2me | Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_map_val_apply
-- name    : GroundTheory.Brauer.SkolemNoether.Twist.map_val_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:55.805651+00:00
-- url     : https://prove2.me/theorems/64b1142e-ff5c-4f83-a2e8-2448560b455c
-- title:
--   Twist: map val apply
-- statement:
--   The Twist construction uses the map val apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L104-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L104-L110

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
open GroundTheory.Brauer.SkolemNoether
variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
open GroundTheory.Brauer.SkolemNoether.Twist
variable (f : B →ₐ[K] A)
variable {f} {g : B →ₐ[K] A}

theorem GroundTheory.Brauer.SkolemNoether.Twist.map_val_apply (φ : Twist f →ₗ[A ⊗[K] Bᵐᵒᵖ] Twist g) (b : B) :
    (φ (of f (f b))).val = (φ (of f 1)).val * g b := by sorry
