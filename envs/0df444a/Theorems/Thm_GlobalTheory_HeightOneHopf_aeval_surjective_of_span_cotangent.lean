-- Prove2me | Theorems.Thm_GlobalTheory_HeightOneHopf_aeval_surjective_of_span_cotangent
-- name    : GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:16:29.489863+00:00
-- url     : https://prove2.me/theorems/7d5550f8-7bc9-4811-be7c-62ae5e125462
-- title:
--   Height One Hopf: aeval surjective of span cotangent
-- statement:
--   The Height One Hopf construction uses the aeval surjective of span cotangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AevalSurjectiveOfSpanCotangent.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AevalSurjectiveOfSpanCotangent.lean#L12-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfIsNilpotentKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfSpanCotangent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.HeightOneHopf

theorem GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) (hnil : IsNilpotent (RingHom.ker ε)) {d : ℕ} (x : Fin d → A)
    (hx : ∀ i, x i ∈ RingHom.ker ε)
    (hspan : ∀ y ∈ RingHom.ker ε, ∃ l : Fin d → R, y - ∑ i, l i • x i ∈ RingHom.ker ε ^ 2) :
    Function.Surjective (MvPolynomial.aeval (R := R) x) := by sorry
