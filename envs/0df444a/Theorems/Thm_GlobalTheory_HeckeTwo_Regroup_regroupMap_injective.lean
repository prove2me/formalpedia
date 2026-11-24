-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_Regroup_regroupMap_injective
-- name    : GlobalTheory.HeckeTwo.Regroup.regroupMap_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:41.4578+00:00
-- url     : https://prove2.me/theorems/d0b71cc2-82a1-4ef1-8f1f-761c7656f01c
-- title:
--   Regroup: regroup Map injective
-- statement:
--   The Regroup construction uses the regroup Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TsumLatticePairUnitQuotientRegroup.lean#L47-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TsumLatticePairUnitQuotientRegroup.lean#L47-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroup
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
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.Regroup
variable {F : Type} [Field F] [NumberField F]
variable (𝔞 𝔟 : Frac F)

theorem GlobalTheory.HeckeTwo.Regroup.regroupMap_injective : Function.Injective (regroupMap 𝔞 𝔟) := by sorry
