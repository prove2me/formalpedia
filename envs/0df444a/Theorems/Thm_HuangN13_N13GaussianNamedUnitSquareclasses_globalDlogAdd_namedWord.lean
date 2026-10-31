-- Prove2me | Theorems.Thm_HuangN13_N13GaussianNamedUnitSquareclasses_globalDlogAdd_namedWord
-- name    : HuangN13.N13GaussianNamedUnitSquareclasses.globalDlogAdd_namedWord
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T07:42:30.334586+00:00
-- url     : https://prove2.me/theorems/8006fdb7-65e6-4489-8e9c-77196d544041
-- title:
--   Ramified logarithm of a named Gaussian unit word
-- statement:
--   For the binary exponent triple c=(i,j,k), the ramified logarithm of its named unit word is i + kα + (j+k)α² in the fixed residue field with basis 1,α,α².
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source: https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13GaussianNamedUnitSquareclasses.lean; exact flattened unit6, lines4002-4012, source-command SHA-256 49689dce4921f274e7def38eb95136d25a3689b7f59f2f60ec9706145e0133c3. Original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GaussianCubicField_integralClosure_eq_adjoin
import Theorems.Thm_MazurProof_N13GaussianCubicField_minpoly_alpha
import Theorems.Thm_MazurProof_N13GaussianGlobalReductionTwo_shiftedTheta_root_h
import Theorems.Thm_MazurProof_N13GaussianNamedUnitSquareclasses_relativeZeta_sq
import Theorems.Thm_MazurProof_N13GaussianOrderTwo_i_sq
import Theorems.Thm_MazurProof_N13LocalDlogRegimes_gaussian_cubic_jet_relation
import Definitions.Def_HuangN13_GaussianUnitLogCore

set_option autoImplicit false
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL

theorem HuangN13.N13GaussianNamedUnitSquareclasses.globalDlogAdd_namedWord (c : MazurProof.N13GaussianNamedUnitSquareclasses.Exp3) :
    MazurProof.N13GaussianNamedUnitSquareclasses.globalDlogAdd (Additive.ofMul (MazurProof.N13GaussianNamedUnitSquareclasses.namedWord c)) =
      (c.1 : MazurProof.N13GaussianNamedUnitSquareclasses.F8) +
        (c.2.2 : MazurProof.N13GaussianNamedUnitSquareclasses.F8) * MazurProof.N13LocalDlogTwo.alpha +
        (c.2.1 + c.2.2 : MazurProof.N13GaussianNamedUnitSquareclasses.F2) *
          MazurProof.N13LocalDlogTwo.alpha ^ 2 := by sorry
