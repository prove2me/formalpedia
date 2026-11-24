-- Prove2me | Theorems.Thm_GlobalTheory_Idele_exists_limit
-- name    : GlobalTheory.Idele.exists_limit
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:52:26.869905+00:00
-- url     : https://prove2.me/theorems/0cf0a606-88c1-41f5-b0fe-ac3f542d9fb2
-- title:
--   Idele: exists limit
-- statement:
--   The Idele construction uses the exists limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L363-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L363-L378

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

theorem GlobalTheory.Idele.exists_limit (v : HeightOneSpectrum R) (u : ℕ → v.adicCompletion K)
    (hu : ∀ m n : ℕ, n ≤ m → Valued.v (u m - u n) ≤ exp (-(n : ℤ))) :
    ∃ t : v.adicCompletion K, ∀ n : ℕ, Valued.v (t - u n) ≤ exp (-(n : ℤ)) := by sorry
