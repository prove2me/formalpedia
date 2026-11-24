-- Prove2me | Theorems.Thm_GlobalTheory_differentiable_rmul_add
-- name    : GlobalTheory.differentiable_rmul_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:30.633851+00:00
-- url     : https://prove2.me/theorems/ddf0d1db-45a6-4221-a0bd-844f802e2e87
-- title:
--   Global Theory: differentiable rmul add
-- statement:
--   The Global Theory construction uses the differentiable rmul add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L215-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L215-L223

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.differentiable_rmul_add {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x I : Frame Ψ r) :
    Differentiable ℂ fun z : Frame Ψ r => rmul x (I + z) := by sorry
