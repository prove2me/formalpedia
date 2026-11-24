-- Prove2me | Theorems.Thm_GlobalTheory_coordinate_const_mono
-- name    : GlobalTheory.coordinate_const_mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:44.557665+00:00
-- url     : https://prove2.me/theorems/e069c94a-5f4f-4557-a999-2bd3494adbe3
-- title:
--   Global Theory: coordinate const mono
-- statement:
--   The Global Theory construction uses the coordinate const mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L221-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L221-L225

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

theorem GlobalTheory.coordinate_const_mono {d g : ℕ} (h : d ≤ g) :
    (d : ℝ) * (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) / 2 - 1) ≤
      (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by sorry
