-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_add_exists
-- name    : GlobalTheory.CubeLift.add_exists
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:28:41.959845+00:00
-- url     : https://prove2.me/theorems/7fca98e4-69c2-42f0-b7c4-5bbd8f8d3a6c
-- title:
--   Cube Lift: add exists
-- statement:
--   The Cube Lift construction uses the add exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L81-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L81-L106

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

theorem GlobalTheory.CubeLift.add_exists (u : A[X × X × X])
    (s₁ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), mv (tri a b c) u = mv (tri b a c) u)
    (s₂ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), mv (tri a b c) u = mv (tri a c b) u)
    (co : ∀ (Y : Type) [AddCommGroup Y] (a b c d : X →+ Y),
      mv (tri (a + b) c d) u + mv (tri a b d) u = mv (tri a (b + c) d) u + mv (tri b c d) u) (a b c : X →+ Y) :
    mv (tri a b c) u = mv (a + b + c) (avg (avg u)) + mv a (avg (avg u)) + mv b (avg (avg u)) + mv c (avg (avg u)) -
      mv (a + b) (avg (avg u)) - mv (a + c) (avg (avg u)) - mv (b + c) (avg (avg u)) := by sorry
