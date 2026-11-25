-- Prove2me | Theorems.Thm_GlobalTheory_NormOneSplit_mem_span_iff
-- name    : GlobalTheory.NormOneSplit.mem_span_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:14.305027+00:00
-- url     : https://prove2.me/theorems/111cb0c3-103f-4fa1-87a5-675fca303717
-- title:
--   Norm One Split: mem span iff
-- statement:
--   The Norm One Split construction uses the mem span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsForallHomEq.lean#L34-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsForallHomEq.lean#L34-L64

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsForallHomEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.NormOneSplit
open NumberField Module Matrix
open scoped ENNReal

theorem GlobalTheory.NormOneSplit.mem_span_iff {E : Type} [Field E] [NumberField E] {T : ℕ}
    (hT : T.Prime)
    (hs : ∀ P : Ideal (𝓞 E), P.IsMaximal → ((T : 𝓞 E) ∈ P) →
      Ideal.absNorm P = T ∧ (T : 𝓞 E) ∉ P ^ 2) (x : 𝓞 E) :
    x ∈ Ideal.span {(T : 𝓞 E)} ↔ ∀ φ : 𝓞 E →+* ZMod T, φ x = 0 := by sorry
