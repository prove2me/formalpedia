-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_del_mem
-- name    : GlobalTheory.CubeLift.del_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:28:18.254646+00:00
-- url     : https://prove2.me/theorems/24541ef4-2b63-4c39-b32a-696b6ccdb1de
-- title:
--   Cube Lift: del mem
-- statement:
--   The Cube Lift construction uses the del mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L199-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L199-L201

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

theorem GlobalTheory.CubeLift.del_mem {I : Ideal A} {g : (A[X])ˣ} (hg : g ∈ cong I) (a b c : X →+ Y) : del g a b c ∈ cong I := by sorry
