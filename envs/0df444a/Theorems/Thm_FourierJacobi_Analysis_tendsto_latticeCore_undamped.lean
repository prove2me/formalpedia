-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_tendsto_latticeCore_undamped
-- name    : FourierJacobi.Analysis.tendsto_latticeCore_undamped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:10:38.241841+00:00
-- url     : https://prove2.me/theorems/0f034249-1d90-5e8e-b8c7-01801612b8fc
-- title:
--   Analysis: tendsto lattice Core undamped
-- statement:
--   Abel convergence is proved by domination of the actual master summand
--   by its summable undamped norm, independently of finite rational continuity.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L52-L73
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L52-L73

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem FourierJacobi.Analysis.tendsto_latticeCore_undamped (q : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt q < ‖d‖) (hd₁ : ‖d‖ ≤ 1) :
    Tendsto (latticeCore q a b d) (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (latticeCore q a b d 1)) := by sorry
