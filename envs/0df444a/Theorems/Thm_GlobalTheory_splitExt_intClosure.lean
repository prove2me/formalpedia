-- Prove2me | Theorems.Thm_GlobalTheory_splitExt_intClosure
-- name    : GlobalTheory.splitExt_intClosure
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:49.924028+00:00
-- url     : https://prove2.me/theorems/b2ecf57f-0e01-4750-baec-1b662e8d087a
-- title:
--   Global Theory: split Ext int Closure
-- statement:
--   The Global Theory construction uses the split Ext int Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCyclotomicSplittingExtension.lean#L7-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCyclotomicSplittingExtension.lean#L7-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCyclotomicSplittingExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.splitExt_intClosure : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (f : Polynomial (FractionRing A)), f ≠ 0 → ∀ q : ℕ, q ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : Algebra A A') (σ : FractionRing A →+* FractionRing A'), Module.Finite A A' ∧ Function.Injective (algebraMap A A') ∧ IsIntegrallyClosed A' ∧ (∃ ζ : A', IsPrimitiveRoot ζ q) ∧ (f.map σ).Splits ∧ σ.comp (algebraMap A (FractionRing A)) = (algebraMap A' (FractionRing A')).comp (algebraMap A A') := by sorry
