-- Prove2me | Theorems.Thm_GlobalTheory_abs_nu_le_of_isRed
-- name    : GlobalTheory.abs_nu_le_of_isRed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:33.06081+00:00
-- url     : https://prove2.me/theorems/7f8cd8bc-a4fe-4b1e-9d10-42f08095eb95
-- title:
--   Global Theory: abs nu le of is Red
-- statement:
--   The Global Theory construction uses the abs nu le of is Red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L81-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsReducedBasisOfLinearIndependent.lean#L81-L120

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

theorem GlobalTheory.abs_nu_le_of_isRed (b : Fin d → E) (hr : IsRed b) (c : Fin d → ℝ) {N : ℝ} (hN : 0 < N)
    (hmin : ∀ w : Fin d → ℤ, ‖∑ l, c l • b l‖ ^ 2 ≤ ‖∑ l, (c l - N * w l) • b l‖ ^ 2)
    (t : Fin d) : |nu b c t| ≤ (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * N := by sorry
