-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_infinite_lattice_special_abel
-- name    : FourierJacobi.Analysis.infinite_lattice_special_abel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:11:24.688234+00:00
-- url     : https://prove2.me/theorems/4e857d0f-9fd6-5fd2-a834-98ede97100ff
-- title:
--   Analysis: infinite lattice special abel
-- statement:
--   The special Abel theorem packages convergence of every damped family,
--   the literal quotient's nonzero denominator, and the whole signed limit.
--   It contains no assertion about an ordinary undamped endpoint family.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L165-L190
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L165-L190

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem FourierJacobi.Analysis.infinite_lattice_special_abel (q : ℝ) (a b ε : ℂ) (hq : 2 < q)
    (hε : ε = 1 ∨ ε = -1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haε : a ≠ ε) (hbε : b ≠ ε) :
    (∀ T ∈ Set.Ioo (0 : ℝ) 1,
      Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
        ‖weightedLatticeTerm q a b (ε * (inverseSqrt q : ℂ)) T p‖) ∧
      HasSum (weightedLatticeTerm q a b (ε * (inverseSqrt q : ℂ)) T)
        (latticeCore q a b (ε * (inverseSqrt q : ℂ)) T)) ∧
    paperC q * paperD1 q a b (ε * (inverseSqrt q : ℂ)) *
      paperD2 q a b (ε * (inverseSqrt q : ℂ)) ≠ 0 ∧
    Tendsto (fun T => ((1 - ε) / ((q : ℂ) + 1)) *
      latticeCore q a b (ε * (inverseSqrt q : ℂ)) T)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - ε) / ((q : ℂ) + 1)) *
        paperE q a b (ε * (inverseSqrt q : ℂ)))) := by sorry
