-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_HermClass_congr_diagonal_of_tail
-- name    : GlobalTheory.LocalQuad.HermClass.congr_diagonal_of_tail
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:52.619588+00:00
-- url     : https://prove2.me/theorems/f1e8f819-5730-46dc-b435-e3968c50eb1d
-- title:
--   Herm Class: congr diagonal of tail
-- statement:
--   The Herm Class construction uses the congr diagonal of tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroCoordNeZero.lean#L68-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroCoordNeZero.lean#L68-L82

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.HermClass
variable {E : Type*} [Field E] {c : E →+* E} {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

theorem GlobalTheory.LocalQuad.HermClass.congr_diagonal_of_tail {r : ℕ} {g g' : Fin (r + 1) → E} (h0 : g 0 = g' 0)
    (h : Congr c (Matrix.diagonal fun i : Fin r => g i.succ)
      (Matrix.diagonal fun i : Fin r => g' i.succ)) :
    Congr c (Matrix.diagonal g) (Matrix.diagonal g') := by sorry
