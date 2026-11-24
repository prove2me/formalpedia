-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_del_mul
-- name    : GlobalTheory.CubeLift.del_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:28:31.662397+00:00
-- url     : https://prove2.me/theorems/47f5b1dd-dacd-4cc1-adc7-a5093cd5a24d
-- title:
--   Cube Lift: del mul
-- statement:
--   The Cube Lift construction uses the del mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L194-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L194-L197

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

theorem GlobalTheory.CubeLift.del_mul (g g' : (A[X])ˣ) (a b c : X →+ Y) : del (g * g') a b c = del g a b c * del g' a b c := by sorry
