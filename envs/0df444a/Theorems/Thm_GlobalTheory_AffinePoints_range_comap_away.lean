-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_range_comap_away
-- name    : GlobalTheory.AffinePoints.range_comap_away
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:53.802476+00:00
-- url     : https://prove2.me/theorems/22a55083-7084-4526-bb3b-fd66e07eef0c
-- title:
--   Affine Points: range comap away
-- statement:
--   The Affine Points construction uses the range comap away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L170-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L170-L180

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

theorem GlobalTheory.AffinePoints.range_comap_away (f : A) [IsLocalization.Away f B] :
    range (comap (IsScalarTower.toAlgHom R A B) : (B →ₐ[R] K) → (A →ₐ[R] K)) = {p | p f ≠ 0} := by sorry
