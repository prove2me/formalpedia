-- Prove2me | Theorems.Thm_GlobalTheory_GaussExt_UnitIdx_pow_mem_range
-- name    : GlobalTheory.GaussExt.UnitIdx.pow_mem_range
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:50:27.44009+00:00
-- url     : https://prove2.me/theorems/78ac7cd1-0951-48a0-89f6-ebf5854227c8
-- title:
--   Unit Idx: pow mem range
-- statement:
--   The Unit Idx construction uses the pow mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteGaussianExtensionUnitsQuotUnits.lean#L89-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteGaussianExtensionUnitsQuotUnits.lean#L89-L131

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

theorem GlobalTheory.GaussExt.UnitIdx.pow_mem_range (u : (𝓞 (Ext F))ˣ) :
    ∃ m : ℕ, 0 < m ∧ u ^ m ∈ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range := by sorry
