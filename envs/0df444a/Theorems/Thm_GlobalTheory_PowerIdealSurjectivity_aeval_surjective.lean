-- Prove2me | Theorems.Thm_GlobalTheory_PowerIdealSurjectivity_aeval_surjective
-- name    : GlobalTheory.PowerIdealSurjectivity.aeval_surjective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:52:52.483779+00:00
-- url     : https://prove2.me/theorems/d5546e8d-ad2e-4f72-9fb9-bc0216c81be7
-- title:
--   Power Ideal Surjectivity: aeval surjective
-- statement:
--   The Power Ideal Surjectivity construction uses the aeval surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpanSubMemSq.lean#L95-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpanSubMemSq.lean#L95-L167

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

theorem GlobalTheory.PowerIdealSurjectivity.aeval_surjective (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Module.Finite O A] [IsLocalRing A] (q : O) (hq : q ∈ IsLocalRing.maximalIdeal O)
    (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (hN : ∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N)
    (hs : Submodule.span O (Set.range fun i ↦ GlobalTheory.AugCot.d ε (x i)) = ⊤) :
    Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O → A) := by sorry
