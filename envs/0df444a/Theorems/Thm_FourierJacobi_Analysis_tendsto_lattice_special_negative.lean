-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_tendsto_lattice_special_negative
-- name    : FourierJacobi.Analysis.tendsto_lattice_special_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:10:52.535485+00:00
-- url     : https://prove2.me/theorems/a8fa89a3-0d03-495c-8f31-92b9b937b128
-- title:
--   Analysis: tendsto lattice special negative
-- statement:
--   The Analysis construction uses the tendsto lattice special negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L98-L116
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L98-L116

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem FourierJacobi.Analysis.tendsto_lattice_special_negative (q : ℝ) (a b : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haM : a ≠ -1) (hbM : b ≠ -1) :
    Tendsto (fun T => ((1 - (-1 : ℂ)) / ((q : ℂ) + 1)) *
      latticeCore q a b (-(inverseSqrt q : ℂ)) T)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - (-1 : ℂ)) / ((q : ℂ) + 1)) *
        paperE q a b (-(inverseSqrt q : ℂ)))) := by sorry
