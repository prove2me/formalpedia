-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_avg_single
-- name    : GlobalTheory.CubeLift.avg_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:09.514128+00:00
-- url     : https://prove2.me/theorems/675538a7-bc79-4ec2-8ee1-863f56aaf105
-- title:
--   Cube Lift: avg single
-- statement:
--   The Cube Lift construction uses the avg single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L30-L34

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
open Classical

theorem GlobalTheory.CubeLift.avg_single (p : X × Y) (r : A) : avg (single p r) = if p.1 = 0 then single p.2 r else 0 := by sorry
