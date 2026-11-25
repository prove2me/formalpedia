-- Prove2me | Theorems.Thm_GlobalTheory_DerivBoundIntegral_wordEnd_mem
-- name    : GlobalTheory.DerivBoundIntegral.wordEnd_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:29:19.388408+00:00
-- url     : https://prove2.me/theorems/45e11ab9-1751-5777-a110-32b2ca40b36a
-- title:
--   Deriv Bound Integral: word End mem
-- statement:
--   The Deriv Bound Integral construction uses the word End mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivWordLeIntegralOfAevalCasimirEqZero.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivWordLeIntegralOfAevalCasimirEqZero.lean#L31-L36

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInteriorEstimateDerivWordPolyLaplacianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SetIntegralNormProdExpMulLeHaarStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftSmoothingProdExpSmoothCommuteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExpStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivWordLeIntegralOfAevalCasimirEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.DerivBoundIntegral
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

theorem GlobalTheory.DerivBoundIntegral.wordEnd_mem (w : List 𝔤) :
    wordEnd h w ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) := by sorry
