-- Prove2me | Theorems.Thm_GlobalTheory_norm_eq_mul_norm_idem_corner
-- name    : GlobalTheory.norm_eq_mul_norm_idem_corner
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:12:23.030997+00:00
-- url     : https://prove2.me/theorems/42bf5bf6-7e3d-4b2d-baa6-11a935acbf59
-- title:
--   Global Theory: norm eq mul norm idem corner
-- statement:
--   The Global Theory construction uses the norm eq mul norm idem corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqMulNormIdempotentCorner.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqMulNormIdempotentCorner.lean#L38-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqMulNormIdempotentCorner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory

theorem GlobalTheory.norm_eq_mul_norm_idem_corner : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A), ψ e = 1 → (∀ a, e * a = algebraMap K A (ψ a) * e) → ∀ a : A, Algebra.norm K a = ψ a * Algebra.norm K (e + (1 - e) * a) := by sorry
