-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_smul_mem_integralPart
-- name    : GlobalTheory.MvPoly.smul_mem_integralPart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:57.889005+00:00
-- url     : https://prove2.me/theorems/ebdbdb9d-09f1-471a-a203-e65778f215ca
-- title:
--   Mv Poly: smul mem integral Part
-- statement:
--   The Mv Poly construction uses the smul mem integral Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L97-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
open GlobalTheory
open GlobalTheory.MvPoly
variable {K σ : Type*} [Field K]

theorem GlobalTheory.MvPoly.smul_mem_integralPart {W : Submodule K (MvPolynomial σ K)} (c : 𝓞 K)
    {P : MvPolynomial σ K} (hP : P ∈ integralPart W) : c • P ∈ integralPart W := by sorry
