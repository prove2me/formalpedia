-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_infinite_lattice_core_evaluation
-- name    : FourierJacobi.Analysis.infinite_lattice_core_evaluation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:11:20.220828+00:00
-- url     : https://prove2.me/theorems/c42455e5-f35d-52e3-8661-eff593cd5900
-- title:
--   Analysis: infinite lattice core evaluation
-- statement:
--   Complete undamped infinite-series evaluation and its Abel convergence,
--   including norm summability and validity of the literal closed quotient.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L145-L160
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L145-L160

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem FourierJacobi.Analysis.infinite_lattice_core_evaluation (q : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt q < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
      ‖weightedLatticeTerm q a b d 1 p‖) ∧
    HasSum (weightedLatticeTerm q a b d 1) (paperE q a b d) ∧
    paperC q * paperD1 q a b d * paperD2 q a b d ≠ 0 ∧
    Tendsto (latticeCore q a b d) (𝓝[Set.Ioo 0 1] 1) (𝓝 (paperE q a b d)) := by sorry
