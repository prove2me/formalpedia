-- Prove2me | Theorems.Thm_MasulloRH_prime_energy_growth_detects_zero_abscissa
-- name    : MasulloRH.prime_energy_growth_detects_zero_abscissa
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:47:02.75035+00:00
-- url     : https://prove2.me/theorems/a8374ba1-02ac-4677-94ad-3ba596898152
-- title:
--   Power growth of finite square-sampled prime energies detects the rightmost zero abscissa
-- statement:
--   For every p≥0, all nontrivial zeros satisfy β≤1/2+p/4 iff E(N)=O_d((N+3)^(p+d)) for every positive d, iff E(N)≤81(N+3)^p for every N. Any individual zero with β>1/2+p/4 forces E(N)>C(N+3)^p past every cutoff and for every C. Ordinary RH is also equivalent to the eventual single sequence of checks E(D_j)≤D_j^(1/(j+1)), where D_j=2^(2^j). Here E(N) is the finite arithmetic energy of the first N perfect-square samples of the actual corrected prime ramp.
-- source:
--   Refinement of the Masullo positive logarithmic energy theorem 0764b70c and square-sampling theorem d932ffd5, for open frontier b41359f9. Uses finite-ordinate estimates, summation by parts for the nonnegative coefficients, and a controlled comparison between squared arithmetic samples and the continuous Mellin energy.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
namespace MasulloRH

theorem prime_energy_growth_detects_zero_abscissa :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let E (N : ℕ) := ∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)
    (∀ p : ℝ, 0≤p →
      ((∀ z : ZetaZerosInTraceStrip (1/2), z.val.re≤1/2+p/4) ↔
        ∀ d : ℝ, 0<d → ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ,E N ≤ C*((N:ℝ)+3)^(p+d)) ∧
      ((∀ z : ZetaZerosInTraceStrip (1/2), z.val.re≤1/2+p/4) ↔
        ∀ N : ℕ,E N ≤ 81*((N:ℝ)+3)^p)) ∧
    (∀ p : ℝ,0≤p → ∀ z : ZetaZerosInTraceStrip (1/2), 1/2+p/4<z.val.re →
      ∀ (C : ℝ) (L : ℕ), ∃ N ≥ L, C*((N:ℝ)+3)^p < E N) ∧
    (RiemannHypothesis ↔ ∃ J : ℕ,∀ j ≥ J, let D := (2:ℕ)^(2^j)
      E D ≤ (D:ℝ)^(1/((j:ℝ)+1))) := by sorry

end MasulloRH
