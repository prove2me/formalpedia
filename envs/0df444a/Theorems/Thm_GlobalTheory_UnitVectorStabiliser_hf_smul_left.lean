-- Prove2me | Theorems.Thm_GlobalTheory_UnitVectorStabiliser_hf_smul_left
-- name    : GlobalTheory.UnitVectorStabiliser.hf_smul_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:22.746575+00:00
-- url     : https://prove2.me/theorems/9a732b8d-d5cd-4328-b00b-12c324c38a83
-- title:
--   Unit Vector Stabiliser: hf smul left
-- statement:
--   The Unit Vector Stabiliser construction uses the hf smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L28-L30

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

theorem GlobalTheory.UnitVectorStabiliser.hf_smul_left (c : A) (x y : n → A) : hform s J (c • x) y = s c * hform s J x y := by sorry
