-- Prove2me | Theorems.Thm_GlobalTheory_HCA_integrable_integral_fin_cons
-- name    : GlobalTheory.HCA.integrable_integral_fin_cons
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:44:14.017948+00:00
-- url     : https://prove2.me/theorems/baf8ff83-a773-4c75-bfb1-480fb2952e0e
-- title:
--   HCA: integrable integral fin cons
-- statement:
--   The HCA construction uses the integrable integral fin cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDixmierMalliavinDecompProdExp.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDixmierMalliavinDecompProdExp.lean#L15-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierMalliavinFactorisationBasisStepStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousLeftTranslateBoundedDerivFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExp
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

theorem GlobalTheory.HCA.integrable_integral_fin_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {F : (Fin (n + 1) → ℝ) → E} (hF : Integrable F) :
    Integrable (fun s : ℝ => ∫ t', F (Fin.cons s t')) := by sorry
