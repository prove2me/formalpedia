-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_weightedLatticeTerm
-- name    : FourierJacobi.Analysis.summable_norm_weightedLatticeTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:09:37.626703+00:00
-- url     : https://prove2.me/theorems/8e9ad39f-2e48-42b1-85bb-8853231e0b90
-- title:
--   Analysis: summable norm weighted Lattice Term
-- statement:
--   The Analysis construction uses the summable norm weighted Lattice Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L77-L97
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L77-L97

import Definitions.Def_FourierJacobi_Analysis_I0Master
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I2Master
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_FourierJacobi_Analysis_LatticeCore
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem FourierJacobi.Analysis.summable_norm_weightedLatticeTerm (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) :
    Summable (fun p : Fin 8 × Fin 3 × LatticeIndex => ‖weightedLatticeTerm q a b d T p‖) := by sorry
