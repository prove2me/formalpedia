-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_isReduced_of_lieReg
-- name    : GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:43.091613+00:00
-- url     : https://prove2.me/theorems/fb7b4111-28cb-4595-8a5c-b518f2c1966f
-- title:
--   Inv Alg: is Reduced of lie Reg
-- statement:
--   The Inv Alg construction uses the is Reduced of lie Reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsReducedOfLieReg.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsReducedOfLieReg.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfLieReg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A := by sorry
