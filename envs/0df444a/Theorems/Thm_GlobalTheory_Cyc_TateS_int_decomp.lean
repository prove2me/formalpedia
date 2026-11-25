-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_TateS_int_decomp
-- name    : GlobalTheory.Cyc.TateS.int_decomp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:21:24.602863+00:00
-- url     : https://prove2.me/theorems/02e76aa8-31f8-4f27-8ed1-2f8ccada8290
-- title:
--   Tate S: int decomp
-- statement:
--   The Tate S construction uses the int decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTateOperatorLevelComplement.lean#L123-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTateOperatorLevelComplement.lean#L123-L143

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.TateS
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.TateS.int_decomp (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) (c : ℕ) : ∀ x : Om l, x ∈ Ks K (j + c) →
    ‖x‖ ≤ 1 → ∃ o ∈ Ks K j, ∃ d ∈ Xalg K j,
      algebraMap (Om l) (PadicComplex l) x = algebraMap (Om l) (PadicComplex l) o + d := by sorry
