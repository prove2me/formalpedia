-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_natural_master_parameters
-- name    : FourierJacobi.Analysis.natural_master_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:09:22.303908+00:00
-- url     : https://prove2.me/theorems/84499378-48a0-57df-9902-4f436ad000cb
-- title:
--   Analysis: natural master parameters
-- statement:
--   The Analysis construction uses the natural master parameters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L66-L75
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean#L66-L75

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

theorem FourierJacobi.Analysis.natural_master_parameters {q : ℝ} (hq : 2 < q) :
    (inverseSqrt q : ℂ) ≠ 0 ∧ (q : ℂ) ≠ 0 ∧
      (q : ℂ) - 1 ≠ 0 ∧ (q : ℂ) - 2 ≠ 0 ∧
      (q : ℂ) * (inverseSqrt q : ℂ) ^ 2 = 1 := by sorry
