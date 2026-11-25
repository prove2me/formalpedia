-- Prove2me | Theorems.Thm_GlobalTheory_CyclotomicTowerSubgroupInclusions_cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified
-- name    : GlobalTheory.CyclotomicTowerSubgroupInclusions.cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:44:46.017049+00:00
-- url     : https://prove2.me/theorems/1d1e8ad7-906c-4e16-a724-0612138c19f1
-- title:
--   Cyclotomic Tower Subgroup Inclusions: cyclotomic Tower Level Galois Subgroup le fixing Unramified
-- statement:
--   The Cyclotomic Tower Subgroup Inclusions construction uses the cyclotomic Tower Level Galois Subgroup le fixing Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateInvariantsCyclotomicTwist.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateInvariantsCyclotomicTwist.lean#L22-L23

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

theorem GlobalTheory.CyclotomicTowerSubgroupInclusions.cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified (K : FinExt l) (j : ℕ) : Gj K j ≤ (K0 K).fixingSubgroup := by sorry
