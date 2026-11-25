-- Prove2me | Theorems.Thm_GlobalTheory_TateDecomp_act_Xj
-- name    : GlobalTheory.TateDecomp.act_Xj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:54.645824+00:00
-- url     : https://prove2.me/theorems/c3e4e802-ec6a-46ca-bf8f-acc70c4fac03
-- title:
--   Tate Decomp: act Xj
-- statement:
--   The Tate Decomp construction uses the act Xj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateDecompositionCompletedCyclotomicIntegers.lean#L137-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateDecompositionCompletedCyclotomicIntegers.lean#L137-L147

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

theorem GlobalTheory.TateDecomp.act_Xj {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {K : FinExt l} {j : ℕ} {g : GQ l} (hg : g ∈ (K0 K).fixingSubgroup) {x : PadicComplex l}
    (hx : x ∈ Xj K j) : act g x ∈ Xj K j := by sorry
