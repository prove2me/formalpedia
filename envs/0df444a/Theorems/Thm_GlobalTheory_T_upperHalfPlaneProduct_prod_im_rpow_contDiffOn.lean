-- Prove2me | Theorems.Thm_GlobalTheory_T_upperHalfPlaneProduct_prod_im_rpow_contDiffOn
-- name    : GlobalTheory.T.upperHalfPlaneProduct_prod_im_rpow_contDiffOn
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:00:36.049601+00:00
-- url     : https://prove2.me/theorems/bc14b93f-ad5f-470b-8f0b-2056b901a8b3
-- title:
--   T: upper Half Plane Product prod im rpow cont Diff On
-- statement:
--   The T construction uses the upper Half Plane Product prod im rpow cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UpperHalfPlaneProductProdImRpowContDiffOnStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UpperHalfPlaneProductProdImRpowContDiffOnStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UpperHalfPlaneProductProdImRpowContDiffOn
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UpperHalfPlaneProductProdImRpowContDiffOnStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.upperHalfPlaneProduct_prod_im_rpow_contDiffOn : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), ContDiffOn ℝ ∞ (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by sorry
