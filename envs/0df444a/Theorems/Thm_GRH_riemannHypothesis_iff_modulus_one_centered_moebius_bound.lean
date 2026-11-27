-- Prove2me | Theorems.Thm_GRH_riemannHypothesis_iff_modulus_one_centered_moebius_bound
-- name    : GRH.riemannHypothesis_iff_modulus_one_centered_moebius_bound
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T23:57:31.16354+00:00
-- url     : https://prove2.me/theorems/3545cb8d-2109-4ffc-a133-2f4d241c8a4b
-- title:
--   The modulus-one centered Möbius power bound is equivalent to the Riemann hypothesis
-- statement:
--   The requested centered bilinear estimate, restricted to q=1 and all exponents strictly between one half and one, holds if and only if ordinary RH holds.
-- source:
--   Exact centered progression bilinear in modulus one. https://prove2.me/theorems/18f77154-a665-45bc-811c-2afbf5a48a5a and https://prove2.me/theorems/b1cc026b-b5ab-5744-b1e2-eaee7b654e01 .

import Definitions.Def_GRH_OneSidedMoebius

theorem GRH.riemannHypothesis_iff_modulus_one_centered_moebius_bound : RiemannHypothesis ↔
    ∀ σ : ℝ, (1/2:ℝ) < σ → σ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear 1 1 N| ≤ C*((N:ℝ)+1)^σ := by sorry
