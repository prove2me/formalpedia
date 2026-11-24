-- Prove2me | Theorems.Thm_GlobalTheory_pairing_const_mono
-- name    : GlobalTheory.pairing_const_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:16.687797+00:00
-- url     : https://prove2.me/theorems/a174c7ed-842e-4707-b60b-fdcc2feb1dd1
-- title:
--   Global Theory: pairing const mono
-- statement:
--   The Global Theory construction uses the pairing const mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L216-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L216-L219

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

theorem GlobalTheory.pairing_const_mono {d g : ℕ} (h : d ≤ g) :
    (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) ≤ (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) := by sorry
