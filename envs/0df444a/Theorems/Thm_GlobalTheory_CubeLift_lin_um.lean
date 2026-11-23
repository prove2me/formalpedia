-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_lin_um
-- name    : GlobalTheory.CubeLift.lin_um
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:17.07625+00:00
-- url     : https://prove2.me/theorems/74abb4e1-1ef1-48ee-a51b-b61dcf995388
-- title:
--   Cube Lift: lin um
-- statement:
--   The Cube Lift construction uses the lin um property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L184-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L184-L185

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

theorem GlobalTheory.CubeLift.lin_um (I : Ideal A) (f : X →+ Y) (u : (A[X])ˣ) : lin I (um f u) = mv f (lin I u) := by sorry
