-- Prove2me | Theorems.Thm_GlobalTheory_UnitVectorStabiliser_hf_add_left
-- name    : GlobalTheory.UnitVectorStabiliser.hf_add_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:39:05.995278+00:00
-- url     : https://prove2.me/theorems/41d71646-3ff4-4ac8-8665-9d658a302e6a
-- title:
--   Unit Vector Stabiliser: hf add left
-- statement:
--   The Unit Vector Stabiliser construction uses the hf add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L21-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabiliser
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (s : A →+* A) (J : Matrix n n A)

theorem GlobalTheory.UnitVectorStabiliser.hf_add_left (x y z : n → A) : hform s J (x + y) z = hform s J x z + hform s J y z := by sorry
