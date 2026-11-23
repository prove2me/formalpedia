-- Prove2me | Theorems.Thm_GlobalTheory_ChebCross_autToPow_eq_iff
-- name    : GlobalTheory.ChebCross.autToPow_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:47.377774+00:00
-- url     : https://prove2.me/theorems/e4d99276-a900-44ff-8ec5-b5444feeaeb3
-- title:
--   Cheb Cross: aut To Pow eq iff
-- statement:
--   The Cheb Cross construction uses the aut To Pow eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobenius.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobenius.lean#L9-L17

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

theorem GlobalTheory.ChebCross.autToPow_eq_iff {m : ℕ} [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) (f : Ω ≃ₐ[F] Ω)
    (j : (ZMod m)ˣ) : hζ.autToPow F f = j ↔ f ζ = ζ ^ (j : ZMod m).val := by sorry
