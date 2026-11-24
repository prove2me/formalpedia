-- Prove2me | Theorems.Thm_GlobalTheory_NakAug_surj
-- name    : GlobalTheory.NakAug.surj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:30:30.522448+00:00
-- url     : https://prove2.me/theorems/a096ed44-eb65-40fb-a7cc-8d6dc1f7afbd
-- title:
--   Nak Aug: surj
-- statement:
--   The Nak Aug construction uses the surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AevalSurjectiveOfCotangentSpanTop.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AevalSurjectiveOfCotangentSpanTop.lean#L8-L15

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanSubMemSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalSurjectiveOfCotangentSpanTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.NakAug

theorem GlobalTheory.NakAug.surj : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by sorry
