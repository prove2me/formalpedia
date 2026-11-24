-- Prove2me | Theorems.Thm_GlobalTheory_Idele_quotEquivAdelic_mulEquiv
-- name    : GlobalTheory.Idele.quotEquivAdelic_mulEquiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:45.562979+00:00
-- url     : https://prove2.me/theorems/a4f42e98-9bdb-4fce-9ba7-9d907153c597
-- title:
--   Idele: quot Equiv Adelic mul Equiv
-- statement:
--   The Idele construction uses the quot Equiv Adelic mul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L506-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L506-L509

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

theorem GlobalTheory.Idele.quotEquivAdelic_mulEquiv (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (hJ : J ≠ 0) (h : J = t • I) (q : K ⧸ (I : Submodule R K)) :
    quotEquivAdelic hJ (mulEquiv t hI h q) = adelicMulEquiv t h (quotEquivAdelic hI q) := by sorry
