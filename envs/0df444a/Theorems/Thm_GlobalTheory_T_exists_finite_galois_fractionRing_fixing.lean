-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finite_galois_fractionRing_fixing
-- name    : GlobalTheory.T.exists_finite_galois_fractionRing_fixing
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:14.604658+00:00
-- url     : https://prove2.me/theorems/e0db98ee-c046-4821-b8b5-f044363a81fc
-- title:
--   T: exists finite galois fraction Ring fixing
-- statement:
--   The T construction uses the exists finite galois fraction Ring fixing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteGaloisFractionRingOfIsFractionRingStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteGaloisFractionRingOfIsFractionRingStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaloisFractionRingOfIsFractionRing
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaloisFractionRingOfIsFractionRingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finite_galois_fractionRing_fixing : ∀ (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L], (∀ a : A, algebraMap A L a = algebraMap K L (algebraMap A K a)) → ∃ (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L), FiniteDimensional (FractionRing A) L ∧ IsGalois (FractionRing A) L ∧ ∀ (σ : L ≃ₐ[FractionRing A] L) (x : K), σ (algebraMap K L x) = algebraMap K L x := by sorry
