-- Prove2me | Theorems.Thm_GlobalTheory_polar_equivFun
-- name    : GlobalTheory.polar_equivFun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:33.71051+00:00
-- url     : https://prove2.me/theorems/9dd7264d-2802-4dc7-84a6-10f45eaacc11
-- title:
--   Global Theory: polar equiv Fun
-- statement:
--   The Global Theory construction uses the polar equiv Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L161-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L161-L169

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module Matrix
open scoped InnerProductSpace TensorProduct MatrixOrder ComplexOrder
open GlobalTheory
open ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2 ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
variable {X : Type*} [AddCommGroup X] {d : ℕ}

theorem GlobalTheory.polar_equivFun (q : QuadraticMap ℤ X ℝ) (b : Basis (Fin d) ℤ X) (x y : X) :
    ReciprocityTheory.ReducedBases.polar (Matrix.of fun i j => QuadraticMap.polar q (b i) (b j))
      (b.equivFun x) (b.equivFun y) = QuadraticMap.polar q x y := by sorry
