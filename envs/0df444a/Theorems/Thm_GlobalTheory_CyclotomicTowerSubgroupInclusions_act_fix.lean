-- Prove2me | Theorems.Thm_GlobalTheory_CyclotomicTowerSubgroupInclusions_act_fix
-- name    : GlobalTheory.CyclotomicTowerSubgroupInclusions.act_fix
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:34:57.033338+00:00
-- url     : https://prove2.me/theorems/ec0b3a0e-a769-4a3c-a0bb-177aa0eb799e
-- title:
--   Cyclotomic Tower Subgroup Inclusions: act fix
-- statement:
--   The Cyclotomic Tower Subgroup Inclusions construction uses the act fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateInvariantsCyclotomicTwist.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateInvariantsCyclotomicTwist.lean#L35-L41

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValIntStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateInvariantsCyclotomicTwist
import Theorems.Thm_GlobalTheory_CycPerturb_act_fix
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CyclotomicTowerSubgroupInclusions
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.CyclotomicTowerSubgroupInclusions.act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by sorry
