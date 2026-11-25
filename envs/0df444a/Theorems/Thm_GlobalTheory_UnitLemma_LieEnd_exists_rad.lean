-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_exists_rad
-- name    : GlobalTheory.UnitLemma.LieEnd.exists_rad
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:03:52.39295+00:00
-- url     : https://prove2.me/theorems/d224d18b-63b7-40d8-82ec-5f02449d6dc6
-- title:
--   Lie End: exists rad
-- statement:
--   The Lie End construction uses the exists rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaSelfAdjointLieOfCountLimitDescent.lean#L105-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaSelfAdjointLieOfCountLimitDescent.lean#L105-L126

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

theorem GlobalTheory.UnitLemma.LieEnd.exists_rad (B : InvAlg K) (h : B.gramDet 1 = 0) :
    ∃ y : B.A, y ≠ 0 ∧ ∀ z, Algebra.trace K.E B.A (y * z) = 0 := by sorry
