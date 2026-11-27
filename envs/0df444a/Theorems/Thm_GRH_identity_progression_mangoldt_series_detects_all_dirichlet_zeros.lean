-- Prove2me | Theorems.Thm_GRH_identity_progression_mangoldt_series_detects_all_dirichlet_zeros
-- name    : GRH.identity_progression_mangoldt_series_detects_all_dirichlet_zeros
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T01:44:58.353946+00:00
-- url     : https://prove2.me/theorems/e96389c6-7b06-458b-ae4a-337b0af9e354
-- title:
--   The identity residue class detects the logarithmic derivative of the full Dirichlet product
-- statement:
--   The regularized product of all Dirichlet L-functions modulo q is entire, is nonzero for Re(s)≥1, and contains every character zero away from the principal pole. For Re(s)>1 the series of von Mangoldt weights in class 1, multiplied by φ(q), equals 1/(s−1) minus the product’s logarithmic derivative.
-- source:
--   Arithmetic reduction for GRH.centered_moebius_progression_bilinear_power_bound. The fixed-modulus equivalence is https://prove2.me/theorems/04e865ba-3dd7-43e6-9714-8e4d666e0b7c . Mathlib.NumberTheory.LSeries.PrimesInAP and DirichletContinuation, at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_GRH_SplitPrimeLower

open GRH.SplitPrimeLower ArithmeticFunction

theorem GRH.identity_progression_mangoldt_series_detects_all_dirichlet_zeros (q : ℕ) [NeZero q] :
    Differentiable ℂ (regularProduct q) ∧
    (∀ s : ℂ, 1 ≤ s.re → regularProduct q s ≠ 0) ∧
    (∀ (χ : DirichletCharacter ℂ q) (s : ℂ), ¬ (χ = 1 ∧ s = 1) →
      regularProduct q s ≠ 0 → χ.LFunction s ≠ 0) ∧
    ∀ s : ℂ, 1 < s.re →
      (q.totient:ℂ) * LSeries (fun n => (vonMangoldt.residueClass (1:ZMod q) n:ℂ)) s =
        1/(s-1) - logDeriv (regularProduct q) s := by sorry
