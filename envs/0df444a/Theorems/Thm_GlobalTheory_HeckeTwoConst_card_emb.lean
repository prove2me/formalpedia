-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoConst_card_emb
-- name    : GlobalTheory.HeckeTwoConst.card_emb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:14:34.138051+00:00
-- url     : https://prove2.me/theorems/48fdae7b-0081-4935-95c6-e5382506faae
-- title:
--   Hecke Two Const: card emb
-- statement:
--   The Hecke Two Const construction uses the card emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoConstantTermEqPartialZetaNegOne.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoConstantTermEqPartialZetaNegOne.lean#L75-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoConstantTermEqPartialZetaNegOne
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
open GlobalTheory GlobalTheory.HeckeTwoConst
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HeckeTwoConst.card_emb [IsTotallyReal F] : Fintype.card (Emb F) = Module.finrank ℚ F := by sorry
