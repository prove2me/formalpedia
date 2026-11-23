-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_rd_mono
-- name    : GlobalTheory.CubeLift.rd_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:45.357893+00:00
-- url     : https://prove2.me/theorems/8c3599ab-a060-46a5-aa8c-12e4d0a92dc4
-- title:
--   Cube Lift: rd mono
-- statement:
--   The Cube Lift construction uses the rd mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L143-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L143-L144

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

theorem GlobalTheory.CubeLift.rd_mono {I I' : Ideal A} (h : I ≤ I') {u : A[X]} (hu : rd I u = 0) : rd I' u = 0 := by sorry
