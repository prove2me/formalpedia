-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_continuousOn_iff
-- name    : GlobalTheory.AffinePoints.continuousOn_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:54:32.007419+00:00
-- url     : https://prove2.me/theorems/2a2425e2-9ffa-492d-8d88-b7531983d689
-- title:
--   Affine Points: continuous On iff
-- statement:
--   The Affine Points construction uses the continuous On iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L29-L31

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
variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [Semiring C] [Algebra R C] [TopologicalSpace C]

theorem GlobalTheory.AffinePoints.continuousOn_iff {X : Type*} [TopologicalSpace X] {f : X → (A →ₐ[R] C)} {s : Set X} :
    ContinuousOn f s ↔ ∀ a, ContinuousOn (fun x => f x a) s := by sorry
