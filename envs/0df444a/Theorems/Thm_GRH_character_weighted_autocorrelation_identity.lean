-- Prove2me | Theorems.Thm_GRH_character_weighted_autocorrelation_identity
-- name    : GRH.character_weighted_autocorrelation_identity
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T17:43:58.810662+00:00
-- url     : https://prove2.me/theorems/4bebd9f0-950e-5d37-afec-aa25454a1776
-- title:
--   Autocorrelation of several rows at the same Dirichlet character
-- statement:
--   On a finite unit group, the character transform of a weighted sum of quotient-count rows is the corresponding weighted sum of squared absolute Fourier coefficients.
-- source:
--   Derived for the centered Möbius theorem in the Masullo mission. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_CharacterMoment

open GRH.CharacterMoment

theorem GRH.character_weighted_autocorrelation_identity (q : ℕ) (χ : DirichletCharacter ℂ q) (I U : Finset ℕ)
    (iv v : ℕ → ℕ) (f : ℕ → ℕ → ℕ) (hp : Permutes q U iv)
    (hu : ∀ b ∈ U, IsUnit (b:ZMod q)) :
    (∑ k ∈ U, ((∑ i ∈ I,v i*(∑ b ∈ U,f i b*f i (b*k%q)) : ℕ):ℂ)*χ (k:ZMod q)) =
      ((∑ i ∈ I,(v i:ℝ)*‖∑ b ∈ U,(f i b:ℂ)*χ (b:ZMod q)‖^2 : ℝ):ℂ) := by sorry
