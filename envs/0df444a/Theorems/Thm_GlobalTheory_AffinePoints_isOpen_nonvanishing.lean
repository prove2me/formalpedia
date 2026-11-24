-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_isOpen_nonvanishing
-- name    : GlobalTheory.AffinePoints.isOpen_nonvanishing
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:55:05.343579+00:00
-- url     : https://prove2.me/theorems/1a150a94-1f78-4d61-b286-688276406002
-- title:
--   Affine Points: is Open nonvanishing
-- statement:
--   The Affine Points construction uses the is Open nonvanishing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L46-L47

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

theorem GlobalTheory.AffinePoints.isOpen_nonvanishing [T1Space C] (f : A) : IsOpen {p : A →ₐ[R] C | p f ≠ 0} := by sorry
