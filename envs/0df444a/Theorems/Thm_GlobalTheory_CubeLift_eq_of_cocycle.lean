-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_eq_of_cocycle
-- name    : GlobalTheory.CubeLift.eq_of_cocycle
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:28:37.161959+00:00
-- url     : https://prove2.me/theorems/29a939bf-ed80-416d-b4e5-5f04b5e3e97f
-- title:
--   Cube Lift: eq of cocycle
-- statement:
--   The Cube Lift construction uses the eq of cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L69-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L69-L79

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

theorem GlobalTheory.CubeLift.eq_of_cocycle (u : A[X × X × W]) (a b : X →+ Y) (w : W →+ Y)
    (h : ∀ (a b c : X →+ X × Y) (w : W →+ X × Y), mv ((a + b).coprod (c.coprod w)) u + mv (a.coprod (b.coprod w)) u =
      mv (a.coprod ((b + c).coprod w)) u + mv (b.coprod (c.coprod w)) u) :
    mv (b.coprod w) (avg u) + mv (a.coprod w) (avg u) =
      mv ((a + b).coprod w) (avg u) + mv (a.coprod (b.coprod w)) u := by sorry
