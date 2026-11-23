-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_lin_del
-- name    : GlobalTheory.CubeLift.lin_del
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:19.043643+00:00
-- url     : https://prove2.me/theorems/18d23547-82a6-405a-ab44-3958660e471f
-- title:
--   Cube Lift: lin del
-- statement:
--   The Cube Lift construction uses the lin del property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L203-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L203-L210

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

theorem GlobalTheory.CubeLift.lin_del {I : Ideal A} {g : (A[X])ˣ} (hg : g ∈ cong I) (a b c : X →+ Y) :
    lin I (del g a b c) = mv (a + b + c) (lin I g) + mv a (lin I g) + mv b (lin I g) + mv c (lin I g) -
      mv (a + b) (lin I g) - mv (a + c) (lin I g) - mv (b + c) (lin I g) := by sorry
