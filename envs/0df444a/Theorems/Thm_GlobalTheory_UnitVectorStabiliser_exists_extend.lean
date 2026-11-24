-- Prove2me | Theorems.Thm_GlobalTheory_UnitVectorStabiliser_exists_extend
-- name    : GlobalTheory.UnitVectorStabiliser.exists_extend
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:38:51.338681+00:00
-- url     : https://prove2.me/theorems/a084c72a-2b2b-4c78-893d-3b5b550cda77
-- title:
--   Unit Vector Stabiliser: exists extend
-- statement:
--   The Unit Vector Stabiliser construction uses the exists extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L76-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean#L76-L113

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

theorem GlobalTheory.UnitVectorStabiliser.exists_extend (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j)
    (hd : IsUnit J.det) (x : n → A) (hx : IsUnit (hform s J x x)) (P : Submodule A (n → A))
    (hP : ∀ y, y ∈ P ↔ hform s J x y = 0) (u : P →ₗ[A] P)
    (hu : ∀ y z : P, hform s J (u y) (u z) = hform s J y z) :
    ∃ g : GL n A, g ∈ UJ s J ∧ (g : Matrix n n A) *ᵥ x = x ∧
      ∀ y : P, (g : Matrix n n A) *ᵥ y = u y := by sorry
