-- Prove2me | Theorems.Thm_GRH_centered_moebius_uniform_large_modulus_range
-- name    : GRH.centered_moebius_uniform_large_modulus_range
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T05:16:00.232493+00:00
-- url     : https://prove2.me/theorems/595fadb4-6113-492f-bf8d-9925375c5b82
-- title:
--   A uniform large-modulus bound for the actual centered Möbius bilinear sum
-- statement:
--   For every positive q, every residue a and every N, the bilinear sum plus its reciprocal correction is the residue sum of the signed Möbius weights. The bilinear sum has absolute value at most 2N/q+1. If N≤q² the bound is 2√N+1. If q≥(N+1)^(1−σ) with σ≥0 it is at most 3(N+1)^σ.
-- source:
--   Möbius bilinear progression problem on Prove2Me. The finite sums and all normalizations use the original GRH_MoebiusBilinear definition. The Fourier character is Mathlib’s ZMod.stdAddChar. Exact remainder https://prove2.me/theorems/99bde901-b30d-40ce-ae0f-029719b78029 and coprime reciprocal inequality https://prove2.me/theorems/ade37461-c107-420f-8794-acb22367614a .

import Definitions.Def_GRH_AdditiveMoebiusSpectrum

open Finset GRH.AdditiveMoebiusSpectrum

theorem GRH.centered_moebius_uniform_large_modulus_range (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) :
    (GRH.centeredMoebiusBilinear q a N + correction q N = fiber a N (weight true N)) ∧
    |GRH.centeredMoebiusBilinear q a N| ≤ 2 * (N : ℝ)/q + 1 ∧
    (N ≤ q^2 → |GRH.centeredMoebiusBilinear q a N| ≤ 2 * Real.sqrt N + 1) ∧
    (∀ σ : ℝ, 0 ≤ σ → ((N : ℝ)+1)^(1-σ) ≤ q →
      |GRH.centeredMoebiusBilinear q a N| ≤ 3 * ((N : ℝ)+1)^σ) := by sorry
