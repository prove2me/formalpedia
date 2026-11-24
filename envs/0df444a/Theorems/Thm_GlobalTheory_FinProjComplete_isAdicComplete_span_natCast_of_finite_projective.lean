-- Prove2me | Theorems.Thm_GlobalTheory_FinProjComplete_isAdicComplete_span_natCast_of_finite_projective
-- name    : GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:41.269618+00:00
-- url     : https://prove2.me/theorems/822bb179-9bd1-46ed-858b-ec1845dd19ae
-- title:
--   Fin Proj Complete: is Adic Complete span nat Cast of finite projective
-- statement:
--   The Fin Proj Complete construction uses the is Adic Complete span nat Cast of finite projective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra.lean#L61-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra.lean#L61-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinProjComplete

theorem GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective (p : ℕ) (O A : Type) [CommRing O] [CommRing A]
    [Algebra O A] [Module.Finite O A] [Module.Projective O A]
    [IsAdicComplete (Ideal.span {(p : O)}) O] : IsAdicComplete (Ideal.span {(p : A)}) A := by sorry
