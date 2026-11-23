-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_um_tri_del
-- name    : GlobalTheory.CubeLift.um_tri_del
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:49.734557+00:00
-- url     : https://prove2.me/theorems/65c5b329-9aec-4719-88b2-41728a8d1188
-- title:
--   Cube Lift: um tri del
-- statement:
--   The Cube Lift construction uses the um tri del property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L223-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L223-L224

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

theorem GlobalTheory.CubeLift.um_tri_del (g : (A[X])ˣ) (a b c : X →+ Y) : um (tri a b c) (del g p₁ p₂ p₃) = del g a b c := by sorry
