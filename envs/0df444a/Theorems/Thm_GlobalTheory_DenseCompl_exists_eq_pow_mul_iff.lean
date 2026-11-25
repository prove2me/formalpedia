-- Prove2me | Theorems.Thm_GlobalTheory_DenseCompl_exists_eq_pow_mul_iff
-- name    : GlobalTheory.DenseCompl.exists_eq_pow_mul_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:09.279509+00:00
-- url     : https://prove2.me/theorems/1abd1f59-5587-5c65-9511-6a7c542546d8
-- title:
--   Dense Compl: exists eq pow mul iff
-- statement:
--   The Dense Compl construction uses the exists eq pow mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqZeroOfForallLeExp.lean#L30-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqZeroOfForallLeExp.lean#L30-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousOfValuationEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqZeroOfForallLeExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open WithZero
open GlobalTheory GlobalTheory.DenseCompl
variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq]

theorem GlobalTheory.DenseCompl.exists_eq_pow_mul_iff {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) (q : Qq) (n : ℕ) :
    (∃ w : W, q = algebraMap W Qq (π ^ n * w)) ↔ v.valuation Qq q ≤ exp (-(n : ℤ)) := by sorry
