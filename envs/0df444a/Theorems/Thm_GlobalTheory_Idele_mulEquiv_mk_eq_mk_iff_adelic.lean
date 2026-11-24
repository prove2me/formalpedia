-- Prove2me | Theorems.Thm_GlobalTheory_Idele_mulEquiv_mk_eq_mk_iff_adelic
-- name    : GlobalTheory.Idele.mulEquiv_mk_eq_mk_iff_adelic
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:03.316505+00:00
-- url     : https://prove2.me/theorems/721f0f1e-77e4-41e5-8c24-4761d3d29948
-- title:
--   Idele: mul Equiv mk eq mk iff adelic
-- statement:
--   The Idele construction uses the mul Equiv mk eq mk iff adelic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L511-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L511-L517

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

theorem GlobalTheory.Idele.mulEquiv_mk_eq_mk_iff_adelic (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = t • I) (x y : K) :
    mulEquiv t hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      (t : 𝔸ᶠ[R, K]) * algebraMap K _ x - algebraMap K _ y ∈ adelicIdeal J := by sorry
