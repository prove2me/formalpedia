-- Prove2me | Theorems.Thm_GlobalTheory_Idele_mulEquiv_mk_eq_mk_iff
-- name    : GlobalTheory.Idele.mulEquiv_mk_eq_mk_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:19.45892+00:00
-- url     : https://prove2.me/theorems/0bd4d211-760a-4c3c-ab0a-0ce39142c893
-- title:
--   Idele: mul Equiv mk eq mk iff
-- statement:
--   The Idele construction uses the mul Equiv mk eq mk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L519-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L519-L524

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

theorem GlobalTheory.Idele.mulEquiv_mk_eq_mk_iff (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = t • I) (x y : K) :
    mulEquiv t hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      ∀ v : HeightOneSpectrum R, (t : 𝔸ᶠ[R, K]) v * algebraMap K (v.adicCompletion K) x -
        algebraMap K (v.adicCompletion K) y ∈ localIdeal v J := by sorry
