-- Prove2me | Theorems.Thm_GlobalTheory_FrobRoot_mm_sum_pow
-- name    : GlobalTheory.FrobRoot.mm_sum_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:29.271806+00:00
-- url     : https://prove2.me/theorems/a72f595f-7666-4b09-b726-8f4f4daf1d76
-- title:
--   Frob Root: mm sum pow
-- statement:
--   The Frob Root construction uses the mm sum pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowAdditiveAndRoots.lean#L56-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowAdditiveAndRoots.lean#L56-L68

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodOfMemSlots
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowAdditiveAndRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds GlobalTheory.LeafTerm
open GlobalTheory GlobalTheory.FrobRoot
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.FrobRoot.mm_sum_pow (e : ℕ) {ι : Type} (s : Finset ι) (x : ι → C) (hx : ∀ i ∈ s, V.Ge 0 (x i)) :
    V.MM ((∑ i ∈ s, x i) ^ (V.l ^ e) - ∑ i ∈ s, x i ^ (V.l ^ e)) := by sorry
