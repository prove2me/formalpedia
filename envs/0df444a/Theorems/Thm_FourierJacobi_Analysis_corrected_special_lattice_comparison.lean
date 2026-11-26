-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_corrected_special_lattice_comparison
-- name    : FourierJacobi.Analysis.corrected_special_lattice_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:10:54.072455+00:00
-- url     : https://prove2.me/theorems/88451808-9207-5b75-a481-2f1e63db9cc4
-- title:
--   Analysis: corrected special lattice comparison
-- statement:
--   Corrected special comparison for the whole product, on the literal
--   endpoint quotient's regular locus. There is no extra normalization factor.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L128-L141
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L128-L141

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem FourierJacobi.Analysis.corrected_special_lattice_comparison (q : ℝ) (a b ε : ℂ) (hq : 2 < q)
    (hε : ε = 1 ∨ ε = -1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haε : a ≠ ε) (hbε : b ≠ ε) :
    Tendsto (fun T => ((1 - ε) / ((q : ℂ) + 1)) *
      latticeCore q a b (ε * (inverseSqrt q : ℂ)) T)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - ε) / ((q : ℂ) + 1)) *
        paperE q a b (ε * (inverseSqrt q : ℂ)))) := by sorry
