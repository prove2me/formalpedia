-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_corrected_principal_lattice_comparison
-- name    : FourierJacobi.Analysis.corrected_principal_lattice_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:11:07.993896+00:00
-- url     : https://prove2.me/theorems/953e73be-eb46-59e6-a6ae-fcf3ca91ba7d
-- title:
--   Analysis: corrected principal lattice comparison
-- statement:
--   Corrected principal comparison at the series scope. The required
--   factor 2/(q+1) multiplies both the Abel limit and E_q.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L86-L96
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L86-L96

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem FourierJacobi.Analysis.corrected_principal_lattice_comparison (q : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt q < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    (2 / ((q : ℂ) + 1) * latticeCore q a b d 1 =
      2 / ((q : ℂ) + 1) * paperE q a b d) ∧
    Tendsto (fun T => 2 / ((q : ℂ) + 1) * latticeCore q a b d T)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (2 / ((q : ℂ) + 1) * paperE q a b d)) := by sorry
