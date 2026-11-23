-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_mv_single
-- name    : GlobalTheory.CubeLift.mv_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:08.23981+00:00
-- url     : https://prove2.me/theorems/4470fe35-b488-49ce-b109-9ec00f6ccd41
-- title:
--   Cube Lift: mv single
-- statement:
--   The Cube Lift construction uses the mv single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L15-L16

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

theorem GlobalTheory.CubeLift.mv_single (f : X →+ Y) (a : X) (r : A) : mv f (single a r) = single (f a) r := by sorry
