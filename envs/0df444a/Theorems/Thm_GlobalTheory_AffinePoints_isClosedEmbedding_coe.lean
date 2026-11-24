-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_isClosedEmbedding_coe
-- name    : GlobalTheory.AffinePoints.isClosedEmbedding_coe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:56.139567+00:00
-- url     : https://prove2.me/theorems/2a424ca8-a4cb-4889-8dc7-37d39127318f
-- title:
--   Affine Points: is Closed Embedding coe
-- statement:
--   The Affine Points construction uses the is Closed Embedding coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L49-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L49-L66

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

theorem GlobalTheory.AffinePoints.isClosedEmbedding_coe [T2Space C] [IsTopologicalSemiring C] :
    IsClosedEmbedding (fun p : A →ₐ[R] C => (p : A → C)) := by sorry
