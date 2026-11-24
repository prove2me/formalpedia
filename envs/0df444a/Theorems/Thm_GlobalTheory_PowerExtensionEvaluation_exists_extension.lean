-- Prove2me | Theorems.Thm_GlobalTheory_PowerExtensionEvaluation_exists_extension
-- name    : GlobalTheory.PowerExtensionEvaluation.exists_extension
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:41.349495+00:00
-- url     : https://prove2.me/theorems/09318546-0d51-4d12-a2a2-5c2f176fd516
-- title:
--   Power Extension Evaluation: exists extension
-- statement:
--   The Power Extension Evaluation construction uses the exists extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/PowLeComapMapPow.lean#L24-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/PowLeComapMapPow.lean#L24-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.PowerExtensionEvaluation

theorem GlobalTheory.PowerExtensionEvaluation.exists_extension {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) [IsAdicComplete (Ideal.map f I) B] :
    ∃ g : AdicCompletion I A →+* B, g.comp (algebraMap A (AdicCompletion I A)) = f := by sorry
