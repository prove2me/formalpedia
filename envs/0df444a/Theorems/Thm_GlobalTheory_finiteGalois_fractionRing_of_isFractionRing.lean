-- Prove2me | Theorems.Thm_GlobalTheory_finiteGalois_fractionRing_of_isFractionRing
-- name    : GlobalTheory.finiteGalois_fractionRing_of_isFractionRing
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:13.859678+00:00
-- url     : https://prove2.me/theorems/5e7018bb-a24f-444c-9175-f94478c9b9e9
-- title:
--   Global Theory: finite Galois fraction Ring of is Fraction Ring
-- statement:
--   The Global Theory construction uses the finite Galois fraction Ring of is Fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteGaloisFractionRingOfIsFractionRing.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteGaloisFractionRingOfIsFractionRing.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaloisFractionRingOfIsFractionRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.finiteGalois_fractionRing_of_isFractionRing :
    ∀ (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L], (∀ a : A, algebraMap A L a = algebraMap K L (algebraMap A K a)) → ∃ (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L), FiniteDimensional (FractionRing A) L ∧ IsGalois (FractionRing A) L ∧ ∀ (σ : L ≃ₐ[FractionRing A] L) (x : K), σ (algebraMap K L x) = algebraMap K L x := by sorry
