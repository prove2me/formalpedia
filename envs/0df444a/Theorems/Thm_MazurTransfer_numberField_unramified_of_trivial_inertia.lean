-- Prove2me | Theorems.Thm_MazurTransfer_numberField_unramified_of_trivial_inertia
-- name    : MazurTransfer.numberField_unramified_of_trivial_inertia
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T11:10:16.584737+00:00
-- url     : https://prove2.me/theorems/34bf7ad3-ae4f-4af9-82f4-869caa6fd890
-- title:
--   Trivial inertia implies unramified integer rings
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields. Suppose that the inertia subgroup of $\mathrm{Gal}(L/K)$ at every maximal ideal of $\mathcal O_L$ is trivial. Then the natural algebra $\mathcal O_K\to\mathcal O_L$ is unramified in the commutative-algebra sense. The proof uses the inertia/ramification-index criterion at each nonzero prime and handles the generic prime separately in characteristic zero.
-- source:
--   MazurTransfer.NumberFieldUnramifiedOfTrivialInertia.unramified_of_trivial_inertia. Uses the unchanged existing-public FLT theorem Ideal.inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable (aa19cb1e-2854-554b-be2a-c5faaea39bf9), complete official source checked at pin 6e837e75355538c7f80bab5b956861e86c4eacc2, and Mathlib local-to-global unramifiedness including the generic point. Applied to the same actual cyclic19 cutout over Q(zeta13).

import Mathlib
open scoped NumberField

theorem MazurTransfer.numberField_unramified_of_trivial_inertia
    (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (hI : ∀ (Q : Ideal (𝓞 L)) [Q.IsMaximal], Q.inertia (L ≃ₐ[K] L) = ⊥) :
    Algebra.Unramified (𝓞 K) (𝓞 L) := by sorry
