-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_lattice_undamped
-- name    : FourierJacobi.Analysis.summable_norm_lattice_undamped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:10:27.694102+00:00
-- url     : https://prove2.me/theorems/5079bf58-7901-4cca-954c-81945073c2fd
-- title:
--   Analysis: summable norm lattice undamped
-- statement:
--   The Analysis construction uses the summable norm lattice undamped property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L26-L33
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L26-L33

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem FourierJacobi.Analysis.summable_norm_lattice_undamped (q : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt q < ‖d‖) (hd₁ : ‖d‖ ≤ 1) :
    Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
      ‖weightedLatticeTerm q a b d 1 p‖) := by sorry
