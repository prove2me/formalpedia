-- Prove2me | Theorems.Thm_GlobalTheory_Idele_mem_smul_iff
-- name    : GlobalTheory.Idele.mem_smul_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:55.511793+00:00
-- url     : https://prove2.me/theorems/e5f4310a-7862-40af-9176-936ad3964c6f
-- title:
--   Idele: mem smul iff
-- statement:
--   The Idele construction uses the mem smul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L273-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L273-L283

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

theorem GlobalTheory.Idele.mem_smul_iff (t : 𝔸ᶠ[R, K]ˣ) {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ t • I ↔ ∃ a ∈ adelicIdeal I, (t : 𝔸ᶠ[R, K]) * a = algebraMap K 𝔸ᶠ[R, K] x := by sorry
