-- Prove2me | Theorems.Thm_GlobalTheory_CycEigen_chiC_mem_inC
-- name    : GlobalTheory.CycEigen.chiC_mem_inC
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:24:06.333866+00:00
-- url     : https://prove2.me/theorems/0ba443eb-829b-4274-8d6d-746ef8282a35
-- title:
--   Cyc Eigen: chi C mem in C
-- statement:
--   The Cyc Eigen construction uses the chi C mem in C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeBis.lean#L136-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormZpowSubOneLeBis.lean#L136-L138

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
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
variable {l : ℕ} [hl : Fact l.Prime]

theorem GlobalTheory.CycEigen.chiC_mem_inC (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g : GQ l)
    (F : IntermediateField ℚ_[l] (Om l)) : chiC χ i g ∈ inC F := by sorry
