-- Prove2me | Theorems.Thm_GlobalTheory_DifferentElement_diff_element
-- name    : GlobalTheory.DifferentElement.diff_element
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:48:44.65649+00:00
-- url     : https://prove2.me/theorems/d09c4e5a-5b70-4d96-b40f-ea25a07ac912
-- title:
--   Different Element: diff element
-- statement:
--   The Different Element construction uses the diff element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDifferentExponentDenominator.lean#L100-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDifferentExponentDenominator.lean#L100-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations UniqueFactorizationMonoid
open GlobalTheory GlobalTheory.DifferentElement
open Classical

theorem GlobalTheory.DifferentElement.diff_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (l : ℕ), l.Prime →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E →
    ∃ D : O, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal →
        val_vp O l (algebraMap O K D) = ((diffExp_vp l P : ℚ) : WithTop ℚ)) ∧
      ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) →
        ∃ z : O, algebraMap O K z = algebraMap O K D * σ y := by sorry
