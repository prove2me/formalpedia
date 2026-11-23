-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_rd_mv
-- name    : GlobalTheory.CubeLift.rd_mv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:36.497136+00:00
-- url     : https://prove2.me/theorems/b5e863d9-2f3f-4f9a-b3d1-b1fb4d3b9db3
-- title:
--   Cube Lift: rd mv
-- statement:
--   The Cube Lift construction uses the rd mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L126-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L126-L127

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

theorem GlobalTheory.CubeLift.rd_mv (I : Ideal A) (f : X →+ Y) (u : A[X]) : rd I (mv f u) = mv f (rd I u) := by sorry
