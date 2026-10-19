-- Prove2me | Theorems.Thm_MazurTransfer_thirteenth_root_galois_quotient_certificates
-- name    : MazurTransfer.thirteenth_root_galois_quotient_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T23:32:48.474031+00:00
-- url     : https://prove2.me/theorems/535b01b8-0d8d-44fd-ba2e-f8489ff71fc5
-- statement:
--   For a primitive thirteenth root in a normal characteristic-zero extension of the rationals, its Galois power map is surjective, its kernel fixes the root, and the generator two has an actual Galois lift sending z to z². The five complete original propositions are retained.

import Mathlib
import Definitions.Def_MazurTransfer_ThirteenToNineteenOriginalCharacterDataAndConstructorCertificates20261018
noncomputable section
universe u
open Polynomial MazurTransfer.ThirteenToNineteenCharacters
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018

theorem MazurTransfer.thirteenth_root_galois_quotient_certificates :
    (∀ (K : Type u) [Field K] [CharZero K] [Normal ℚ K] (z : K) (hz : IsPrimitiveRoot z 13)
    (σ : K ≃ₐ[ℚ] K) (u : (ZMod 13)ˣ) (hσ : σ z = z ^ (u : ZMod 13).val),
    hz.autToPow ℚ σ = u) ∧
    (∀ (K : Type u) [Field K] [CharZero K] [Normal ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) (u : (ZMod 13)ˣ),
    ∃ σ : K ≃ₐ[ℚ] K, σ z = z ^ (u : ZMod 13).val) ∧
    (∀ (K : Type u) [Field K] [CharZero K] [Normal ℚ K] (z : K) (hz : IsPrimitiveRoot z 13), Function.Surjective (hz.autToPow ℚ)) ∧
    (∀ (K : Type u) [Field K] [CharZero K] [Normal ℚ K] (z : K) (hz : IsPrimitiveRoot z 13)
    (σ : K ≃ₐ[ℚ] K) (hσ : hz.autToPow ℚ σ = 1), σ z = z) ∧
    (∀ (K : Type u) [Field K] [CharZero K] [Normal ℚ K] (z : K) (hz : IsPrimitiveRoot z 13),
    ∃ σ : K ≃ₐ[ℚ] K, σ z = z ^ 2 ∧ hz.autToPow ℚ σ = generator) := by sorry
