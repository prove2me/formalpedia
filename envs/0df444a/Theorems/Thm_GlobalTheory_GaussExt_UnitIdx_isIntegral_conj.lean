-- Prove2me | Theorems.Thm_GlobalTheory_GaussExt_UnitIdx_isIntegral_conj
-- name    : GlobalTheory.GaussExt.UnitIdx.isIntegral_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:50:16.209524+00:00
-- url     : https://prove2.me/theorems/41190327-d5a7-4633-b190-cb9d813be676
-- title:
--   Unit Idx: is Integral conj
-- statement:
--   The Unit Idx construction uses the is Integral conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteGaussianExtensionUnitsQuotUnits.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteGaussianExtensionUnitsQuotUnits.lean#L86-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaussianExtensionUnitsQuotUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.GaussExt GlobalTheory.GaussExt.UnitIdx
variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]

theorem GlobalTheory.GaussExt.UnitIdx.isIntegral_conj {x : Ext F} (hx : IsIntegral ℤ x) : IsIntegral ℤ (conj F x) := by sorry
