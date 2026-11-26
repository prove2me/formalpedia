-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_lattice_damped
-- name    : FourierJacobi.Analysis.summable_norm_lattice_damped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:10:13.371594+00:00
-- url     : https://prove2.me/theorems/2ff055c7-1184-56c8-af0e-fbebc695920d
-- title:
--   Analysis: summable norm lattice damped
-- statement:
--   The Analysis construction uses the summable norm lattice damped property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L17-L24
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean#L17-L24

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem FourierJacobi.Analysis.summable_norm_lattice_damped (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hT₀ : 0 < T) (hT₁ : T < 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1) :
    Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
      ‖weightedLatticeTerm q a b d T p‖) := by sorry
