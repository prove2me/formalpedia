-- Prove2me | Theorems.Thm_GlobalTheory_Idele_exists_idealOf_eq
-- name    : GlobalTheory.Idele.exists_idealOf_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:04:05.905809+00:00
-- url     : https://prove2.me/theorems/4c9864ba-b8e3-48c2-88f9-d207d6366e39
-- title:
--   Idele: exists ideal Of eq
-- statement:
--   The Idele construction uses the exists ideal Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L308-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L308-L327

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

theorem GlobalTheory.Idele.exists_idealOf_eq {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∃ t : 𝔸ᶠ[R, K]ˣ, idealOf t = I := by sorry
