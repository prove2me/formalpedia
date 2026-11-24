-- Prove2me | Theorems.Thm_GlobalTheory_PlancherelZero_fourB_sub
-- name    : GlobalTheory.PlancherelZero.fourB_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:44:37.794794+00:00
-- url     : https://prove2.me/theorems/2b2da5af-d278-4322-bfb0-59d5c3704406
-- title:
--   Plancherel Zero: four B sub
-- statement:
--   The Plancherel Zero construction uses the four B sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTruncatedFourierTendstoZeroEtale.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTruncatedFourierTendstoZeroEtale.lean#L39-L44

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

theorem GlobalTheory.PlancherelZero.fourB_sub (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μ : Measure A.K)
    [IsFiniteMeasureOnCompacts μ] {f g : A.K → ℂ} (hf : IsTest f) (hg : IsTest g) (y : A.K) :
    fourB μ (A.kerK ψ) (f - g) y = fourB μ (A.kerK ψ) f y - fourB μ (A.kerK ψ) g y := by sorry
