-- Prove2me | Theorems.Thm_GlobalTheory_PowerIdealSurjectivity_exists_span_sub_mem_sq
-- name    : GlobalTheory.PowerIdealSurjectivity.exists_span_sub_mem_sq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:52:58.360931+00:00
-- url     : https://prove2.me/theorems/4ef7a867-a345-4c2c-af81-d043107c521b
-- title:
--   Power Ideal Surjectivity: exists span sub mem sq
-- statement:
--   The Power Ideal Surjectivity construction uses the exists span sub mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpanSubMemSq.lean#L7-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpanSubMemSq.lean#L7-L46

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanSubMemSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerIdealSurjectivity
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

theorem GlobalTheory.PowerIdealSurjectivity.exists_span_sub_mem_sq (ε : A →ₐ[O] O) {d : ℕ} (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (hs : Submodule.span O (Set.range fun i ↦ GlobalTheory.AugCot.d ε (x i)) = ⊤) {c : A}
    (hc : c ∈ RingHom.ker ε) :
    ∃ m ∈ Submodule.span O (Set.range x), m ∈ RingHom.ker ε ∧ c - m ∈ RingHom.ker ε ^ 2 := by sorry
