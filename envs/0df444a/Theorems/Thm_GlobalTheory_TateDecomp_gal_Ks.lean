-- Prove2me | Theorems.Thm_GlobalTheory_TateDecomp_gal_Ks
-- name    : GlobalTheory.TateDecomp.gal_Ks
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:38.13299+00:00
-- url     : https://prove2.me/theorems/0fae808e-a114-4f97-b81d-0cab1c87daf5
-- title:
--   Tate Decomp: gal Ks
-- statement:
--   The Tate Decomp construction uses the gal Ks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateDecompositionCompletedCyclotomicIntegers.lean#L121-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateDecompositionCompletedCyclotomicIntegers.lean#L121-L135

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

theorem GlobalTheory.TateDecomp.gal_Ks {K : FinExt l} {g : GQ l} (hg : g ∈ (K0 K).fixingSubgroup) (i : ℕ) {w : Om l}
    (hw : w ∈ Ks K i) : g w ∈ Ks K i := by sorry
