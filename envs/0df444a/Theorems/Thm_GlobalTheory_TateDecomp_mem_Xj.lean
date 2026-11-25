-- Prove2me | Theorems.Thm_GlobalTheory_TateDecomp_mem_Xj
-- name    : GlobalTheory.TateDecomp.mem_Xj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:36.011715+00:00
-- url     : https://prove2.me/theorems/7e03e1ec-aaac-490e-a490-dab120b3925e
-- title:
--   Tate Decomp: mem Xj
-- statement:
--   The Tate Decomp construction uses the mem Xj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateDecompositionCompletedCyclotomicIntegers.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateDecompositionCompletedCyclotomicIntegers.lean#L98-L99

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

theorem GlobalTheory.TateDecomp.mem_Xj {K : FinExt l} {j : ℕ} {x : PadicComplex l} :
    x ∈ Xj K j ↔ x ∈ closure (Xsum K j : Set (PadicComplex l)) := by sorry
