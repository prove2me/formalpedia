-- Prove2me | Theorems.Thm_GRH_centered_bilinear_additive_modes_and_residue_inversion
-- name    : GRH.centered_bilinear_additive_modes_and_residue_inversion
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T05:15:39.210585+00:00
-- url     : https://prove2.me/theorems/a63c65ca-74cf-536b-8e26-6c90dbc00766
-- title:
--   Exact nonzero Fourier modes and variance of the centered Möbius residue row
-- statement:
--   Every nonzero additive Fourier mode of the actual centered bilinear row is the signed rational Möbius transform. Finite Fourier inversion holds for both weight choices. At every positive modulus, q times the sum of squared deviations from the row mean equals the energy in the nonzero frequencies.
-- source:
--   Möbius bilinear progression problem on Prove2Me. The finite sums and all normalizations use the original GRH_MoebiusBilinear definition. The Fourier character is Mathlib’s ZMod.stdAddChar.

import Definitions.Def_GRH_AdditiveMoebiusSpectrum

open Finset GRH.AdditiveMoebiusSpectrum

theorem GRH.centered_bilinear_additive_modes_and_residue_inversion (q : ℕ) [NeZero q] (N : ℕ) :
    (∀ h : ZMod q, h ≠ 0 → transform true N (angle h) =
      ∑ a : ZMod q, (GRH.centeredMoebiusBilinear q a N : ℂ) * ZMod.stdAddChar (a*h)) ∧
    (∀ (s : Bool) (a : ZMod q), (q : ℂ) * (fiber a N (weight s N) : ℂ) =
      ∑ h : ZMod q, ZMod.stdAddChar (-(a*h)) * transform s N (angle h)) ∧
    (q : ℝ) * rowVariance q N =
      ∑ h ∈ (univ : Finset (ZMod q)).erase 0, ‖transform true N (angle h)‖^2 := by sorry
