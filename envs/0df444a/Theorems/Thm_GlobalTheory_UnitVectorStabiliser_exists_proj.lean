-- Prove2me | Theorems.Thm_GlobalTheory_UnitVectorStabiliser_exists_proj
-- name    : GlobalTheory.UnitVectorStabiliser.exists_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:17.449813+00:00
-- url     : https://prove2.me/theorems/e5b82bac-4d0e-4bce-91ed-51a772263ef5
-- title:
--   Unit Vector Stabiliser: exists proj
-- statement:
--   The Unit Vector Stabiliser construction uses the exists proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L58-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L58-L74

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

theorem GlobalTheory.UnitVectorStabiliser.exists_proj (x : n → A) (hx : IsUnit (hform s J x x)) (P : Submodule A (n → A))
    (hP : ∀ y, y ∈ P ↔ hform s J x y = 0) :
    ∃ (c : (n → A) →ₗ[A] A) (p : (n → A) →ₗ[A] P), (∀ y, y = c y • x + (p y : n → A)) ∧
      c x = 1 ∧ ∀ y : P, c y = 0 := by sorry
