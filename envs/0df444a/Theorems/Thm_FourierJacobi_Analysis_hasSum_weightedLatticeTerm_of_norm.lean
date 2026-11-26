-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_weightedLatticeTerm_of_norm
-- name    : FourierJacobi.Analysis.hasSum_weightedLatticeTerm_of_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:09:28.256854+00:00
-- url     : https://prove2.me/theorems/b845ad69-0b0d-570c-89a1-23c689826846
-- title:
--   Analysis: has Sum weighted Lattice Term of norm
-- statement:
--   The full unordered family has the independently defined core as its sum.
--   The hypothesis is absolute summability of this family, proved above from the
--   natural parameter bounds; no rearrangement is made before that proof.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L122-L137
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L122-L137

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

theorem FourierJacobi.Analysis.hasSum_weightedLatticeTerm_of_norm (q T : ℝ) (a b d : ℂ)
    (hn : Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
      ‖weightedLatticeTerm q a b d T p‖)) :
    HasSum (weightedLatticeTerm q a b d T) (latticeCore q a b d T) := by sorry
