-- Prove2me | Theorems.Thm_GlobalTheory_Idele_mulEquiv_mem_iff
-- name    : GlobalTheory.Idele.mulEquiv_mem_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:21.762803+00:00
-- url     : https://prove2.me/theorems/f2dc23be-8c20-48f7-a130-98d875b62a21
-- title:
--   Idele: mul Equiv mem iff
-- statement:
--   The Idele construction uses the mul Equiv mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L573-L581
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L573-L581

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

theorem GlobalTheory.Idele.mulEquiv_mem_iff (t : 𝔸ᶠ[R, K]ˣ) {I J I' : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = t • I) (hle : I ≤ I') {x y : K}
    (hxy : mulEquiv t hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) :
    y ∈ t • I' ↔ x ∈ I' := by sorry
