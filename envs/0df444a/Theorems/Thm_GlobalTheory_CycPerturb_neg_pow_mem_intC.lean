-- Prove2me | Theorems.Thm_GlobalTheory_CycPerturb_neg_pow_mem_intC
-- name    : GlobalTheory.CycPerturb.neg_pow_mem_intC
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:22:06.711924+00:00
-- url     : https://prove2.me/theorems/641561a4-7ec9-5ed5-83e9-aa1d1c40ae09
-- title:
--   Cyc Perturb: neg pow mem int C
-- statement:
--   The Cyc Perturb construction uses the neg pow mem int C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerGeneratorMatrixPerturbation.lean#L261-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerGeneratorMatrixPerturbation.lean#L261-L264

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

theorem GlobalTheory.CycPerturb.neg_pow_mem_intC {F : IntermediateField ℚ_[l] (Om l)} {x : PadicComplex l}
    (hx : x ∈ intC F) (k : ℕ) : (-x) ^ k ∈ intC F := by sorry
