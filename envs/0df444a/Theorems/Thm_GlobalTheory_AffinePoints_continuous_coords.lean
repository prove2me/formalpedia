-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_continuous_coords
-- name    : GlobalTheory.AffinePoints.continuous_coords
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:54:35.251831+00:00
-- url     : https://prove2.me/theorems/067aa242-2374-4242-b2b8-7c578d093892
-- title:
--   Affine Points: continuous coords
-- statement:
--   The Affine Points construction uses the continuous coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L89-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set
open MvPolynomial
variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] [TopologicalSpace C] {σ : Type*}

theorem GlobalTheory.AffinePoints.continuous_coords (g : MvPolynomial σ R →ₐ[R] A) :
    Continuous (coords g : (A →ₐ[R] C) → σ → C) := by sorry
