-- Prove2me | Theorems.Thm_GlobalTheory_finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord
-- name    : GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:27.815612+00:00
-- url     : https://prove2.me/theorems/4988f422-4e58-4178-8a3d-7c88cece32fb
-- title:
--   Global Theory: finsum ord mul inertia Deg eq finrank mul ord
-- statement:
--   The Global Theory construction uses the finsum ord mul inertia Deg eq finrank mul ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumOrdMulInertiaDegEqFinrankMulOrd.lean#L171-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumOrdMulInertiaDegEqFinrankMulOrd.lean#L171-L248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumOrdMulInertiaDegEqFinrankMulOrd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open IsLocalRing
open scoped Pointwise

theorem GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord (A B : Type) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] (hinj : Function.Injective (algebraMap A B)) (hdim : ringKrullDim A = 1)
    (a : A) (ha : a ≠ 0) :
    ∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A},
      ((Ring.ord (Localization.AtPrime Q.asIdeal)
        (algebraMap B _ (algebraMap A B a))).toNat : ℤ) * (Q.asIdeal.inertiaDeg A : ℤ) =
      (Module.finrank A B : ℤ) * ((Ring.ord A a).toNat : ℤ) := by sorry
