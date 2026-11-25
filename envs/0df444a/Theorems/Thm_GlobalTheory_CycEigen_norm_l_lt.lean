-- Prove2me | Theorems.Thm_GlobalTheory_CycEigen_norm_l_lt
-- name    : GlobalTheory.CycEigen.norm_l_lt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:33:27.877804+00:00
-- url     : https://prove2.me/theorems/4eea3a4f-4f74-410e-a454-2048b89cd173
-- title:
--   Cyc Eigen: norm l lt
-- statement:
--   The Cyc Eigen construction uses the norm l lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalProdEqZeroHodgeTateCyclotomicFrame.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalProdEqZeroHodgeTateCyclotomicFrame.lean#L40-L42

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrame
import Theorems.Thm_GlobalTheory_TateDecomp_norm_l_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.CycEigen.norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by sorry
