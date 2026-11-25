-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_TateS_Xalg_le_of
-- name    : GlobalTheory.Cyc.TateS.Xalg_le_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:30.277349+00:00
-- url     : https://prove2.me/theorems/6816ba5c-b269-5aba-a772-32d8357caa25
-- title:
--   Tate S: Xalg le of
-- statement:
--   The Tate S construction uses the Xalg le of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTateOperatorLevelComplement.lean#L101-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTateOperatorLevelComplement.lean#L101-L110

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

theorem GlobalTheory.Cyc.TateS.Xalg_le_of (K : FinExt l) (j : ℕ) (B : AddSubgroup (PadicComplex l))
    (h : ∀ i, j < i → ∀ z y : Om l, IsPrimitiveRoot z (l ^ i) → y ∈ Ks K (i - 1) → ‖y‖ ≤ 1 →
      algebraMap (Om l) (PadicComplex l) (z * y) ∈ B) : Xalg K j ≤ B := by sorry
