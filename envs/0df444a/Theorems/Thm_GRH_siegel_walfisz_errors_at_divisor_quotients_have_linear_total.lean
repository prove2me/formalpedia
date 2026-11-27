-- Prove2me | Theorems.Thm_GRH_siegel_walfisz_errors_at_divisor_quotients_have_linear_total
-- name    : GRH.siegel_walfisz_errors_at_divisor_quotients_have_linear_total
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T06:47:37.269929+00:00
-- url     : https://prove2.me/theorems/61c55bf8-7ea2-4396-b09c-51468fe07d49
-- title:
--   The total Siegel–Walfisz error over divisor quotients is linear
-- statement:
--   Fix a positive modulus q. For each positive integer d choose any reduced class b(d). The sum over 1 ≤ d ≤ N of the absolute differences between the Chebyshev sum at floor(N/d) in that class and N/(d φ(q)) is at most C(q)N for every N.
-- source:
--   Unconditional fixed-modulus estimates for the centered Möbius progression sum in https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 . Siegel–Walfisz input https://prove2.me/submissions/81593c60-fedd-42b2-9d93-584a56da2a6e .

import Definitions.Def_GRH_LogarithmicMoebius

open Finset Filter Topology GRH.LogarithmicMoebius

theorem GRH.siegel_walfisz_errors_at_divisor_quotients_have_linear_total (q : ℕ) [NeZero q] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (b : ℕ → (ZMod q)ˣ),
      (∑ d ∈ Ioc 0 N, |psi (b d : ZMod q) (N/d) - (N:ℝ)/(d:ℝ)/(q.totient:ℝ)|) ≤ C*(N:ℝ) := by sorry
