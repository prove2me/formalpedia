-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_cyclotomic_splitting_extension
-- name    : GlobalTheory.T.exists_cyclotomic_splitting_extension
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:28:46.331689+00:00
-- url     : https://prove2.me/theorems/ad6d54a2-646d-5e09-addf-5edd0df2e6b6
-- title:
--   T: exists cyclotomic splitting extension
-- statement:
--   The T construction uses the exists cyclotomic splitting extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCyclotomicSplittingExtensionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCyclotomicSplittingExtensionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCyclotomicSplittingExtension
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCyclotomicSplittingExtensionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_cyclotomic_splitting_extension : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (f : Polynomial (FractionRing A)), f ≠ 0 → ∀ q : ℕ, q ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : Algebra A A') (σ : FractionRing A →+* FractionRing A'), Module.Finite A A' ∧ Function.Injective (algebraMap A A') ∧ IsIntegrallyClosed A' ∧ (∃ ζ : A', IsPrimitiveRoot ζ q) ∧ (f.map σ).Splits ∧ σ.comp (algebraMap A (FractionRing A)) = (algebraMap A' (FractionRing A')).comp (algebraMap A A') := by sorry
