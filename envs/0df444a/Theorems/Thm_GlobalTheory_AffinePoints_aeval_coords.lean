-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_aeval_coords
-- name    : GlobalTheory.AffinePoints.aeval_coords
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:12.492263+00:00
-- url     : https://prove2.me/theorems/5d07757f-3e4b-4f57-aa44-5863c76bc84b
-- title:
--   Affine Points: aeval coords
-- statement:
--   The Affine Points construction uses the aeval coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L84-L87

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
omit [TopologicalSpace C]

theorem GlobalTheory.AffinePoints.aeval_coords (g : MvPolynomial σ R →ₐ[R] A) (p : A →ₐ[R] C) (q : MvPolynomial σ R) :
    aeval (coords g p) q = p (g q) := by sorry
