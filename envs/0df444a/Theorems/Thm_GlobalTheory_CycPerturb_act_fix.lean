-- Prove2me | Theorems.Thm_GlobalTheory_CycPerturb_act_fix
-- name    : GlobalTheory.CycPerturb.act_fix
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:11:41.78631+00:00
-- url     : https://prove2.me/theorems/8fefc73e-286f-5c96-a670-9d30bf1bf6e2
-- title:
--   Cyc Perturb: act fix
-- statement:
--   The Cyc Perturb construction uses the act fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerGeneratorMatrixPerturbation.lean#L289-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerGeneratorMatrixPerturbation.lean#L289-L295

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation
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
open GlobalTheory GlobalTheory.CycPerturb
variable {l : ℕ} [hl : Fact l.Prime]

theorem GlobalTheory.CycPerturb.act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act)
    {K : FinExt l} {j : ℕ} {g : GQ l} (hg : g ∈ Gj K j) {y : PadicComplex l}
    (hy : y ∈ inC (Ks K j)) : act g y = y := by sorry
