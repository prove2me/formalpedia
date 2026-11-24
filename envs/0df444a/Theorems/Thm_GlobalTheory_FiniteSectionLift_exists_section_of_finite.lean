-- Prove2me | Theorems.Thm_GlobalTheory_FiniteSectionLift_exists_section_of_finite
-- name    : GlobalTheory.FiniteSectionLift.exists_section_of_finite
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:30.170078+00:00
-- url     : https://prove2.me/theorems/c777cd62-aba7-497a-b86e-76c598affaf5
-- title:
--   Finite Section Lift: exists section of finite
-- statement:
--   The Finite Section Lift construction uses the exists section of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSectionOfFinite.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSectionOfFinite.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSectionOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FiniteSectionLift

theorem GlobalTheory.FiniteSectionLift.exists_section_of_finite (R A K : CommRingCat) (φ : R ⟶ K)
    (hinj : Function.Injective φ.hom)
    (hint : ∀ x : K, φ.hom.IsIntegralElem x → ∃ r : R, φ.hom r = x)
    (g : R ⟶ A) (hg : g.hom.Finite) (f : A ⟶ K) (hf : g ≫ f = φ) :
    ∃ s : A ⟶ R, g ≫ s = 𝟙 R ∧ s ≫ φ = f := by sorry
