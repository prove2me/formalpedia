-- Prove2me | Theorems.Thm_GlobalTheory_Idele_eq_zero_of_forall_mul_mem
-- name    : GlobalTheory.Idele.eq_zero_of_forall_mul_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:51:49.608039+00:00
-- url     : https://prove2.me/theorems/a1a67350-cc78-41a8-8a6d-88440497f7ea
-- title:
--   Idele: eq zero of forall mul mem
-- statement:
--   The Idele construction uses the eq zero of forall mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L704-L714
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L704-L714

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
open GlobalTheory GlobalTheory.Idele
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem GlobalTheory.Idele.eq_zero_of_forall_mul_mem {J : FractionalIdeal R⁰ K} (hJ : J ≠ 0) {t : 𝔸ᶠ[R, K]}
    (h : ∀ x : K, t * algebraMap K 𝔸ᶠ[R, K] x ∈ adelicIdeal J) : t = 0 := by sorry
