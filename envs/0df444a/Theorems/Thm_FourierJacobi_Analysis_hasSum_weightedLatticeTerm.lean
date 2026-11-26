-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_weightedLatticeTerm
-- name    : FourierJacobi.Analysis.hasSum_weightedLatticeTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:09:36.017618+00:00
-- url     : https://prove2.me/theorems/cf7266a8-239c-4b80-bd73-c072b671fb3b
-- title:
--   Analysis: has Sum weighted Lattice Term
-- statement:
--   The Analysis construction uses the has Sum weighted Lattice Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L139-L146
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L139-L146

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

theorem FourierJacobi.Analysis.hasSum_weightedLatticeTerm (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) :
    HasSum (weightedLatticeTerm q a b d T) (latticeCore q a b d T) := by sorry
