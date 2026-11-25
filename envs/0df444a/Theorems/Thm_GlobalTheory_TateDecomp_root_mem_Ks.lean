-- Prove2me | Theorems.Thm_GlobalTheory_TateDecomp_root_mem_Ks
-- name    : GlobalTheory.TateDecomp.root_mem_Ks
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:51:43.959341+00:00
-- url     : https://prove2.me/theorems/54284a8f-945c-5dc2-aeb4-1aba4e2c716c
-- title:
--   Tate Decomp: root mem Ks
-- statement:
--   The Tate Decomp construction uses the root mem Ks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateDecompositionCompletedCyclotomicIntegers.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateDecompositionCompletedCyclotomicIntegers.lean#L42-L43

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.TateDecomp.root_mem_Ks (K : FinExt l) {i : ℕ} {x : Om l} (hx : x ^ (l ^ i) = 1) : x ∈ Ks K i := by sorry
