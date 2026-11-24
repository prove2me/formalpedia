-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_finite_fiber_comap
-- name    : GlobalTheory.AffinePoints.finite_fiber_comap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:34.493732+00:00
-- url     : https://prove2.me/theorems/25e87765-4f48-4a4d-99ea-fdc210cf4187
-- title:
--   Affine Points: finite fiber comap
-- statement:
--   The Affine Points construction uses the finite fiber comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L47-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set Polynomial
variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

theorem GlobalTheory.AffinePoints.finite_fiber_comap {R A B K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [Field K] [Algebra R K] (φ : A →ₐ[R] B) (hφ : φ.Finite) (p : A →ₐ[R] K) :
    ((comap φ : (B →ₐ[R] K) → (A →ₐ[R] K)) ⁻¹' {p}).Finite := by sorry
