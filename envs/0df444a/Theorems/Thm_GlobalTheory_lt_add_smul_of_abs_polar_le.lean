-- Prove2me | Theorems.Thm_GlobalTheory_lt_add_smul_of_abs_polar_le
-- name    : GlobalTheory.lt_add_smul_of_abs_polar_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:01.606809+00:00
-- url     : https://prove2.me/theorems/391cf817-9e89-4935-a407-18ba3bda3525
-- title:
--   Global Theory: lt add smul of abs polar le
-- statement:
--   The Global Theory construction uses the lt add smul of abs polar le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L202-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L202-L214

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

theorem GlobalTheory.lt_add_smul_of_abs_polar_le (q : QuadraticMap ℤ X ℝ) {e μ : X} {c : ℝ} {N : ℤ}
    (hc : 0 ≤ c) (hN : 2 * c < N) (hμ : 0 < q μ)
    (h : |QuadraticMap.polar q e μ| ≤ c * QuadraticMap.polar q μ μ) :
    q e < q (e + N • μ) ∧ q (-e) < q (-e + N • μ) := by sorry
