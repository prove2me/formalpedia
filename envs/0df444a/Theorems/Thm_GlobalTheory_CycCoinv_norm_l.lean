-- Prove2me | Theorems.Thm_GlobalTheory_CycCoinv_norm_l
-- name    : GlobalTheory.CycCoinv.norm_l
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:41.446046+00:00
-- url     : https://prove2.me/theorems/beeff8e0-17ab-5e19-af6d-03667f76642d
-- title:
--   Cyc Coinv: norm l
-- statement:
--   The Cyc Coinv construction uses the norm l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorsionCoinvariantsTwistedCyclotomicGenerator.lean#L111-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorsionCoinvariantsTwistedCyclotomicGenerator.lean#L111-L112

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator
import Theorems.Thm_GlobalTheory_Cyc_TateS_norm_l
import Theorems.Thm_GlobalTheory_UnramValue_norm_l

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.CycCoinv
variable {l : ℕ} [hl : Fact l.Prime]

theorem GlobalTheory.CycCoinv.norm_l : ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := by sorry
