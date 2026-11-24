-- Prove2me | Theorems.Thm_GlobalTheory_ChebCross_exists_fixing
-- name    : GlobalTheory.ChebCross.exists_fixing
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:02.889695+00:00
-- url     : https://prove2.me/theorems/595a7e77-e4ec-4687-9ff6-0b99c6514873
-- title:
--   Cheb Cross: exists fixing
-- statement:
--   The Cheb Cross construction uses the exists fixing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobenius.lean#L19-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobenius.lean#L19-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicCrossingFieldDecidingFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.ChebCross
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

theorem GlobalTheory.ChebCross.exists_fixing [CharZero Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) (hirr : Irreducible (cyclotomic m L))
    (j : (ZMod m)ˣ) : ∃ u : Ω ≃ₐ[F] Ω, u ∈ L.fixingSubgroup ∧ hζ.autToPow F u = j := by sorry
