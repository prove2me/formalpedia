-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_tendsto_master_sum_of_summable
-- name    : FourierJacobi.Analysis.tendsto_master_sum_of_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:37:21.137288+00:00
-- url     : https://prove2.me/theorems/d1392182-e903-52ee-a893-87249ced45b5
-- title:
--   Analysis: tendsto master sum of summable
-- statement:
--   Dominated convergence on the actual master family. The summability
--   input is deliberately visible and is discharged by the region assembly.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterDamping.lean#L66-L73
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterDamping.lean#L66-L73

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations Filter
open scoped Topology

theorem FourierJacobi.Analysis.tendsto_master_sum_of_summable (q t d U V : ℂ) (r : ℤ)
    (hs : Summable (fun p : LatticeIndex => ‖masterTerm q t d U V 1 r p‖)) :
    Tendsto (fun T : ℝ => ∑' p : LatticeIndex, masterTerm q t d U V (T : ℂ) r p)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (∑' p : LatticeIndex, masterTerm q t d U V 1 r p)) := by sorry
