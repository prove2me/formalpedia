-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_TateS_mem_Xalg
-- name    : GlobalTheory.Cyc.TateS.mem_Xalg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:12:51.924315+00:00
-- url     : https://prove2.me/theorems/55e14b6a-c84c-4dba-a6a5-ade7d0c3be44
-- title:
--   Tate S: mem Xalg
-- statement:
--   The Tate S construction uses the mem Xalg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTateOperatorLevelComplement.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTateOperatorLevelComplement.lean#L112-L117

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

theorem GlobalTheory.Cyc.TateS.mem_Xalg (K : FinExt l) {j i : ℕ} (hi : j < i) {z y : Om l}
    (hz : IsPrimitiveRoot z (l ^ i)) (hy : y ∈ Ks K (i - 1)) (hy1 : ‖y‖ ≤ 1) :
    algebraMap (Om l) (PadicComplex l) (z * y) ∈ Xalg K j := by sorry
