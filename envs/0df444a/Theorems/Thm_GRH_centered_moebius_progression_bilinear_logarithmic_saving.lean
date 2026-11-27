-- Prove2me | Theorems.Thm_GRH_centered_moebius_progression_bilinear_logarithmic_saving
-- name    : GRH.centered_moebius_progression_bilinear_logarithmic_saving
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T06:47:37.340797+00:00
-- url     : https://prove2.me/theorems/f41d0c6a-7277-40bf-9b1e-aefca52e5b03
-- title:
--   Unconditional logarithmic cancellation for the centered Möbius bilinear progression sum
-- statement:
--   For each fixed positive q there is C(q) such that all reduced residues a and all N satisfy |B(q,a,N)| ≤ min(2N/q+1, C(q)N/(1+log(N+1))). The nonnegative centering correction is at most C(q)N/[q(1+log(N+1))²]. Consequently |B(q,a,N)|/N tends to zero uniformly over the reduced residues modulo q.
-- source:
--   Unconditional fixed-modulus estimates for the centered Möbius progression sum in https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 . Signed fiber and pointwise input https://prove2.me/submissions/dc0048dc-5648-4712-8b8c-07d527bc5d09 .

import Definitions.Def_GRH_LogarithmicMoebius

open Finset Filter Topology GRH.LogarithmicMoebius

theorem GRH.centered_moebius_progression_bilinear_logarithmic_saving (q : ℕ) [NeZero q] :
    ∃ C : ℝ, 0 ≤ C ∧
    (∀ N : ℕ, 0 ≤ GRH.AdditiveMoebiusSpectrum.correction q N ∧
      GRH.AdditiveMoebiusSpectrum.correction q N*(scale N)^2 ≤ C*(N:ℝ)/q) ∧
    (∀ (a : ZMod q), IsUnit a → ∀ N : ℕ, |GRH.centeredMoebiusBilinear q a N| ≤
      min (2*(N:ℝ)/q+1) (C*(N:ℝ)/scale N)) ∧
    (∀ ε : ℝ, 0<ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ a : ZMod q, IsUnit a →
      |GRH.centeredMoebiusBilinear q a N| ≤ ε*(N:ℝ)) := by sorry
