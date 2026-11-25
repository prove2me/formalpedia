-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_trace_prod
-- name    : GlobalTheory.UnitLemma.LieEnd.trace_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:03:12.318461+00:00
-- url     : https://prove2.me/theorems/053b06bc-5ed5-5614-9e75-f68d6741a3d6
-- title:
--   Lie End: trace prod
-- statement:
--   The Lie End construction uses the trace prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaSelfAdjointLieOfCountLimitDescent.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaSelfAdjointLieOfCountLimitDescent.lean#L53-L54

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

theorem GlobalTheory.UnitLemma.LieEnd.trace_prod (B₁ B₂ : InvAlg K) (x : B₁.A × B₂.A) :
    Algebra.trace K.E (B₁.A × B₂.A) x = Algebra.trace K.E B₁.A x.1 + Algebra.trace K.E B₂.A x.2 := by sorry
