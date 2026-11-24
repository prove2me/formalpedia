-- Prove2me | Theorems.Thm_GlobalTheory_Idele_existsUnique_adele_of_linearMap
-- name    : GlobalTheory.Idele.existsUnique_adele_of_linearMap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:49.434988+00:00
-- url     : https://prove2.me/theorems/625f5187-0286-4888-83ce-714cff424ff4
-- title:
--   Idele: exists Unique adele of linear Map
-- statement:
--   The Idele construction uses the exists Unique adele of linear Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L716-L729
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L716-L729

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

theorem GlobalTheory.Idele.existsUnique_adele_of_linearMap {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (φ : (K ⧸ (I : Submodule R K)) →ₗ[R] (K ⧸ (J : Submodule R K))) :
    ∃! t : 𝔸ᶠ[R, K], ∀ x : K, quotEquivAdelic hJ (φ (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (t * algebraMap K 𝔸ᶠ[R, K] x) := by sorry
