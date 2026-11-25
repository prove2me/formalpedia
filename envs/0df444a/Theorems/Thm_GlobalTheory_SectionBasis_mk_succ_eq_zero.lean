-- Prove2me | Theorems.Thm_GlobalTheory_SectionBasis_mk_succ_eq_zero
-- name    : GlobalTheory.SectionBasis.mk_succ_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:51:23.889327+00:00
-- url     : https://prove2.me/theorems/1a5b4890-cd86-5f55-a3f9-2fc9f6ee6f76
-- title:
--   Section Basis: mk succ eq zero
-- statement:
--   The Section Basis construction uses the mk succ eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L76-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L76-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']

theorem GlobalTheory.SectionBasis.mk_succ_eq_zero {A : Type} [CommRing A] {D : ℕ} (s : Fin (D + 1) → A)
    (I : Ideal (Localization.Away (s 0)))
    (hI : I = Ideal.span (Set.range fun i : Fin D =>
      algebraMap A (Localization.Away (s 0)) (s i.succ) * IsLocalization.Away.invSelf (s 0))) (i : Fin D) :
    Ideal.Quotient.mk I (algebraMap A (Localization.Away (s 0)) (s i.succ)) = 0 := by sorry
