-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_mulLeft_prod
-- name    : GlobalTheory.UnitLemma.LieEnd.mulLeft_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:07:07.99013+00:00
-- url     : https://prove2.me/theorems/473efacf-8c51-5507-966a-e62ff15c0d0b
-- title:
--   Lie End: mul Left prod
-- statement:
--   The Lie End construction uses the mul Left prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaSelfAdjointLieOfCountLimitDescent.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaSelfAdjointLieOfCountLimitDescent.lean#L45-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaSelfAdjointLieOfCountLimitDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.LieEnd
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ}

theorem GlobalTheory.UnitLemma.LieEnd.mulLeft_prod (B₁ B₂ : InvAlg K) (x : B₁.A × B₂.A) :
    LinearMap.mulLeft K.E x = (LinearMap.mulLeft K.E x.1).prodMap (LinearMap.mulLeft K.E x.2) := by sorry
