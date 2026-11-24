-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_um_del
-- name    : GlobalTheory.CubeLift.um_del
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:29:36.203271+00:00
-- url     : https://prove2.me/theorems/9b04edac-9f48-43a2-a58a-0e4cbd28d2a3
-- title:
--   Cube Lift: um del
-- statement:
--   The Cube Lift construction uses the um del property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L190-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L190-L192

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

theorem GlobalTheory.CubeLift.um_del (f : Y →+ W) (g : (A[X])ˣ) (a b c : X →+ Y) :
    um f (del g a b c) = del g (f.comp a) (f.comp b) (f.comp c) := by sorry
