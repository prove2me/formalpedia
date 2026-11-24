-- Prove2me | Theorems.Thm_GlobalTheory_Idele_mulEquiv_unitEmbedding_mk
-- name    : GlobalTheory.Idele.mulEquiv_unitEmbedding_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:05:02.478+00:00
-- url     : https://prove2.me/theorems/3ee879ed-2a5c-46d2-897a-f8497b5aeee2
-- title:
--   Idele: mul Equiv unit Embedding mk
-- statement:
--   The Idele construction uses the mul Equiv unit Embedding mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L543-L548
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L543-L548

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

theorem GlobalTheory.Idele.mulEquiv_unitEmbedding_mk (c : Kˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = FiniteAdeleRing.unitEmbedding R K c • I) (x : K) :
    mulEquiv (FiniteAdeleRing.unitEmbedding R K c) hI h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((c : K) * x) := by sorry
