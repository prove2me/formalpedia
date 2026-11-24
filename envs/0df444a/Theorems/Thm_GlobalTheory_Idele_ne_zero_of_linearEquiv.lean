-- Prove2me | Theorems.Thm_GlobalTheory_Idele_ne_zero_of_linearEquiv
-- name    : GlobalTheory.Idele.ne_zero_of_linearEquiv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:04:15.052824+00:00
-- url     : https://prove2.me/theorems/dcc44875-9b48-4131-b454-542fe3de2535
-- title:
--   Idele: ne zero of linear Equiv
-- statement:
--   The Idele construction uses the ne zero of linear Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L739-L757
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L739-L757

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

theorem GlobalTheory.Idele.ne_zero_of_linearEquiv {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (φ : (K ⧸ (I : Submodule R K)) ≃ₗ[R] (K ⧸ (J : Submodule R K))) : J ≠ 0 := by sorry
