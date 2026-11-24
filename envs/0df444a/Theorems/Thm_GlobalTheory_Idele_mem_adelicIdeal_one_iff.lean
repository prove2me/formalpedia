-- Prove2me | Theorems.Thm_GlobalTheory_Idele_mem_adelicIdeal_one_iff
-- name    : GlobalTheory.Idele.mem_adelicIdeal_one_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:20.6643+00:00
-- url     : https://prove2.me/theorems/fd4fdeed-3d22-45ec-9f50-d8ea83f50f81
-- title:
--   Idele: mem adelic Ideal one iff
-- statement:
--   The Idele construction uses the mem adelic Ideal one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L583-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L583-L585

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

theorem GlobalTheory.Idele.mem_adelicIdeal_one_iff {a : 𝔸ᶠ[R, K]} :
    a ∈ adelicIdeal (1 : FractionalIdeal R⁰ K) ↔ ∀ v, Valued.v (a v) ≤ 1 := by sorry
