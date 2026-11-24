-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_add_unique
-- name    : GlobalTheory.CubeLift.add_unique
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:28:12.952655+00:00
-- url     : https://prove2.me/theorems/47f762ec-f454-477c-bfd9-84966f8d6411
-- title:
--   Cube Lift: add unique
-- statement:
--   The Cube Lift construction uses the add unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L108-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L108-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
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
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]

theorem GlobalTheory.CubeLift.add_unique (h : A[X]) (H : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y),
    mv (a + b + c) h + mv a h + mv b h + mv c h - mv (a + b) h - mv (a + c) h - mv (b + c) h = 0) : h = 0 := by sorry
