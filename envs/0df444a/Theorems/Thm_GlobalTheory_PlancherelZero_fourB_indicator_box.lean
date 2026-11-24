-- Prove2me | Theorems.Thm_GlobalTheory_PlancherelZero_fourB_indicator_box
-- name    : GlobalTheory.PlancherelZero.fourB_indicator_box
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:44:53.319651+00:00
-- url     : https://prove2.me/theorems/a896c84d-d83f-4ec4-8212-81f624702c97
-- title:
--   Plancherel Zero: four B indicator box
-- statement:
--   The Plancherel Zero construction uses the four B indicator box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTruncatedFourierTendstoZeroEtale.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTruncatedFourierTendstoZeroEtale.lean#L103-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.PlancherelZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.PlancherelZero.fourB_indicator_box (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.K) (u : A.K → ℂ) (c : F)
    (hM : MeasurableSet (box A c)) (y : A.K) :
    fourB μ (A.kerK ψ) ((box A c).indicator u) y = ∫ z in box A c, u z * A.psiK ψ (-((-y) * z)) ∂μ := by sorry
