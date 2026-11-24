-- Prove2me | Theorems.Thm_GlobalTheory_Idele_exists_adele_of_end_one
-- name    : GlobalTheory.Idele.exists_adele_of_end_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:48.002692+00:00
-- url     : https://prove2.me/theorems/54c4999e-386a-4be8-a218-febbf8cba91c
-- title:
--   Idele: exists adele of end one
-- statement:
--   The Idele construction uses the exists adele of end one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L587-L689
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L587-L689

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

theorem GlobalTheory.Idele.exists_adele_of_end_one
    (ψ : (𝔸ᶠ[R, K] ⧸ adelicIdeal (1 : FractionalIdeal R⁰ K)) →ₗ[R]
      (𝔸ᶠ[R, K] ⧸ adelicIdeal (1 : FractionalIdeal R⁰ K))) :
    ∃ t : 𝔸ᶠ[R, K], ∀ a, ψ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (t * a) := by sorry
