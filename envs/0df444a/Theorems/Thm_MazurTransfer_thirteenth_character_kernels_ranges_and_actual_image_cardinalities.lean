-- Prove2me | Theorems.Thm_MazurTransfer_thirteenth_character_kernels_ranges_and_actual_image_cardinalities
-- name    : MazurTransfer.thirteenth_character_kernels_ranges_and_actual_image_cardinalities
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T00:48:39.088713+00:00
-- url     : https://prove2.me/theorems/21563195-b43c-4494-a109-a7da07ecd4ee
-- statement:
--   The explicit arithmetic13 characters have the original kernels {1,generator^6}, generated ranges and six-element images. Both actual primitive-root Galois characters have those exact ranges and image cardinalities. The ten complete original propositions are retained, including the original normal-extension hypotheses on actual Galois fields.

import Mathlib
import Definitions.Def_MazurTransfer_ThirteenToNineteenOriginalCharacterDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualThirteenthCyclotomicReflectedCharacterOriginalData20261018
import Theorems.Thm_MazurTransfer_thirteen_to_nineteen_character_certificates
import Theorems.Thm_MazurTransfer_thirteenth_root_galois_quotient_certificates
noncomputable section
open MazurTransfer.ThirteenToNineteenCharacters MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018

theorem MazurTransfer.thirteenth_character_kernels_ranges_and_actual_image_cardinalities :
    (∀  (u : (ZMod 13)ˣ) ,
    character u = 1 ↔ u = 1 ∨ u = generator ^ 6) ∧
    (∀  (u : (ZMod 13)ˣ) ,
    conjugateCharacter u = 1 ↔ u = 1 ∨ u = generator ^ 6) ∧
    (((generator ^ 6 : (ZMod 13)ˣ) : ZMod 13) = (-1 : ZMod 13)) ∧
    (∀  (χ : (ZMod 13)ˣ →* (ZMod 19)ˣ) ,
    χ.range = Subgroup.zpowers (χ generator)) ∧
    (Nat.card character.range = 6) ∧
    (Nat.card conjugateCharacter.range = 6) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    (piReflectedCharacter K z hz).range = character.range) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    (piConjugateReflectedCharacter K z hz).range = conjugateCharacter.range) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    Nat.card (piReflectedCharacter K z hz).range = 6) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    Nat.card (piConjugateReflectedCharacter K z hz).range = 6) := by sorry
