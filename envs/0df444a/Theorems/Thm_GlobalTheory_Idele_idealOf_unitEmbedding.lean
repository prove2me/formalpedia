-- Prove2me | Theorems.Thm_GlobalTheory_Idele_idealOf_unitEmbedding
-- name    : GlobalTheory.Idele.idealOf_unitEmbedding
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:29.314292+00:00
-- url     : https://prove2.me/theorems/7023c108-f81c-4eb5-91ec-e55e3e0b3cbd
-- title:
--   Idele: ideal Of unit Embedding
-- statement:
--   The Idele construction uses the ideal Of unit Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L285-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L285-L293

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

theorem GlobalTheory.Idele.idealOf_unitEmbedding (x : Kˣ) :
    idealOf (FiniteAdeleRing.unitEmbedding R K x) = FractionalIdeal.spanSingleton R⁰ (x : K) := by sorry
