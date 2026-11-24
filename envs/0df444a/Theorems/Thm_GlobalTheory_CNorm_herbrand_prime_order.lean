-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_herbrand_prime_order
-- name    : GlobalTheory.CNorm.herbrand_prime_order
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:55.019709+00:00
-- url     : https://prove2.me/theorems/fcebca8c-a80e-48a7-9709-43338ec0c7b5
-- title:
--   CNorm: herbrand prime order
-- statement:
--   The CNorm construction uses the herbrand prime order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HerbrandPrimeOrder.lean#L91-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HerbrandPrimeOrder.lean#L91-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowPrimeRangeEqIteratedDifferenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionFiniteKerRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormDifferenceIndexIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexRangeKerIterateEndomorphismStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
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

theorem GlobalTheory.CNorm.herbrand_prime_order : ∀ (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A), p.Prime → (∀ a, σ^[p] a = a) → pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → (nrm σ p).range.relIndex (fix σ) ≠ 0 ∧ (dif σ).range.relIndex (nrm σ p).ker ≠ 0 ∧ pIdx p (fix σ) ≠ 0 ∧ pTor p (fix σ) ≠ 0 ∧ (nrm σ p).range.relIndex (fix σ) ^ (p - 1) * pIdx p (⊤ : Subgroup A) * pTor p (fix σ) ^ p = (dif σ).range.relIndex (nrm σ p).ker ^ (p - 1) * pTor p (⊤ : Subgroup A) * pIdx p (fix σ) ^ p := by sorry
