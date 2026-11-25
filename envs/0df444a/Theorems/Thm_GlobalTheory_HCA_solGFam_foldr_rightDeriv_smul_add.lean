-- Prove2me | Theorems.Thm_GlobalTheory_HCA_solGFam_foldr_rightDeriv_smul_add
-- name    : GlobalTheory.HCA.solGFam_foldr_rightDeriv_smul_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:29:33.515659+00:00
-- url     : https://prove2.me/theorems/960a35c4-8f8e-5b96-a448-2d0857a69a8e
-- title:
--   HCA: sol GFam foldr right Deriv smul add
-- statement:
--   The HCA construction uses the sol GFam foldr right Deriv smul add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaplacePolynomialKernelDerivativeWordsFamily.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaplacePolynomialKernelDerivativeWordsFamily.lean#L33-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivWordLeIntegralOfAevalCasimirEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftTranslateSmoothCommuteLeftInvariantOpsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaplacePolynomialKernelDerivativeWordsFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

theorem GlobalTheory.HCA.solGFam_foldr_rightDeriv_smul_add (l : List 𝔤) {f f' : G → ℂ} (hf : h.IsSmoothFun f)
    (hf' : h.IsSmoothFun f') (c : ℂ) :
    l.foldr h.rightDeriv (c • f + f') = c • l.foldr h.rightDeriv f + l.foldr h.rightDeriv f' := by sorry
