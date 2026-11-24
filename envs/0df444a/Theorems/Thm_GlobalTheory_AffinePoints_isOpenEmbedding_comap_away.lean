-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_isOpenEmbedding_comap_away
-- name    : GlobalTheory.AffinePoints.isOpenEmbedding_comap_away
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:56.665677+00:00
-- url     : https://prove2.me/theorems/ff04f48e-5888-46af-909b-dd1ddd4482b6
-- title:
--   Affine Points: is Open Embedding comap away
-- statement:
--   The Affine Points construction uses the is Open Embedding comap away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L187-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L187-L211

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
variable {R A B K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B] [Field K] [Algebra R K]

theorem GlobalTheory.AffinePoints.isOpenEmbedding_comap_away (f : A) [IsLocalization.Away f B]
    [TopologicalSpace K] [T1Space K] [IsTopologicalDivisionRing K] :
    IsOpenEmbedding (comap (IsScalarTower.toAlgHom R A B) : (B →ₐ[R] K) → (A →ₐ[R] K)) := by sorry
