-- Prove2me | Theorems.Thm_GlobalTheory_CycPerturb_mul_mem_intC
-- name    : GlobalTheory.CycPerturb.mul_mem_intC
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:44:12.890453+00:00
-- url     : https://prove2.me/theorems/810191c6-ce11-44b2-a24a-a80c1b63fabd
-- title:
--   Cyc Perturb: mul mem int C
-- statement:
--   The Cyc Perturb construction uses the mul mem int C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerGeneratorMatrixPerturbation.lean#L256-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerGeneratorMatrixPerturbation.lean#L256-L259

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycPerturb
variable {l : ℕ} [hl : Fact l.Prime]

theorem GlobalTheory.CycPerturb.mul_mem_intC {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l}
    (hx : x ∈ intC F) (hy : y ∈ intC F) : x * y ∈ intC F := by sorry
