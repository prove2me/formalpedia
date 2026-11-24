-- Prove2me | Theorems.Thm_GlobalTheory_norm_scale_idem_add_compl
-- name    : GlobalTheory.norm_scale_idem_add_compl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:05.603688+00:00
-- url     : https://prove2.me/theorems/7d42b6fb-1729-4cd4-90f2-449f43af3f24
-- title:
--   Global Theory: norm scale idem add compl
-- statement:
--   The Global Theory construction uses the norm scale idem add compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqMulNormIdempotentCorner.lean#L6-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqMulNormIdempotentCorner.lean#L6-L36

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

theorem GlobalTheory.norm_scale_idem_add_compl {K A : Type} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A) (he : ψ e = 1)
    (hea : ∀ a, e * a = algebraMap K A (ψ a) * e) (c : K) :
    Algebra.norm K (algebraMap K A c * e + (1 - e)) = c := by sorry
