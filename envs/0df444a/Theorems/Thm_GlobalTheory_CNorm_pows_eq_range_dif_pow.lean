-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_pows_eq_range_dif_pow
-- name    : GlobalTheory.CNorm.pows_eq_range_dif_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:54.485482+00:00
-- url     : https://prove2.me/theorems/7f617c8a-bbd7-424e-82cf-8301514bb8b8
-- title:
--   CNorm: pows eq range dif pow
-- statement:
--   The CNorm construction uses the pows eq range dif pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PowPrimeRangeEqIteratedDifference.lean#L90-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PowPrimeRangeEqIteratedDifference.lean#L90-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowPrimeRangeEqIteratedDifference
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial
open scoped WithZero TensorProduct

theorem GlobalTheory.CNorm.pows_eq_range_dif_pow : ∀ (p : ℕ) (M : Type) [CommGroup M] (τ : M →* M)
    (lam : Monoid.End M), p.Prime → (∀ a, lam a = τ a / a) →
    (∀ a, _root_.GlobalTheory.CNorm.nrm τ p a = 1) →
    _root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup M) = MonoidHom.range (lam ^ (p - 1) : Monoid.End M) ∧
      ∀ a : M, a ^ p = 1 ↔ (lam ^ (p - 1) : Monoid.End M) a = 1 := by sorry
