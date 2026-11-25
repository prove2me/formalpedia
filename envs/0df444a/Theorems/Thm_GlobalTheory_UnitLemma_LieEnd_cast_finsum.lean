-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_cast_finsum
-- name    : GlobalTheory.UnitLemma.LieEnd.cast_finsum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:05:25.309228+00:00
-- url     : https://prove2.me/theorems/e0edf99e-0062-4ae9-8d12-cb7732ae9977
-- title:
--   Lie End: cast finsum
-- statement:
--   The Lie End construction uses the cast finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaSelfAdjointLieOfCountLimitDescent.lean#L135-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaSelfAdjointLieOfCountLimitDescent.lean#L135-L135

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

theorem GlobalTheory.UnitLemma.LieEnd.cast_finsum {ι : Type} (f : ι → ℚ) : ((∑ᶠ i, f i : ℚ) : ℝ) = ∑ᶠ i, (f i : ℝ) := by sorry
