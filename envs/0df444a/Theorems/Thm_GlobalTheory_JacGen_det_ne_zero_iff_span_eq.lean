-- Prove2me | Theorems.Thm_GlobalTheory_JacGen_det_ne_zero_iff_span_eq
-- name    : GlobalTheory.JacGen.det_ne_zero_iff_span_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:45:54.963929+00:00
-- url     : https://prove2.me/theorems/69e88d71-8ed4-4250-9713-6049bfbd7862
-- title:
--   Jac Gen: det ne zero iff span eq
-- statement:
--   The Jac Gen construction uses the det ne zero iff span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacNeZeroIffSpanEqMaximalIdeal.lean#L20-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacNeZeroIffSpanEqMaximalIdeal.lean#L20-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JacGen
open IsLocalRing

theorem GlobalTheory.JacGen.det_ne_zero_iff_span_eq {K S : Type} [Field K] [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra K S] {n : ℕ} (u : S →ₐ[K] K) (D : Fin n → S →ₗ[K] K)
    (hD : ∀ k a b, D k (a * b) = u a * D k b + u b * D k a)
    (hinj : ∀ c : Fin n → K, (∀ a, ∑ k, D k a * c k = 0) → c = 0)
    (hsurj : ∀ δ : S →ₗ[K] K, (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
      ∃ c : Fin n → K, ∀ a, δ a = ∑ k, D k a * c k)
    (f : Fin n → S) (hf : ∀ i, u (f i) = 0) :
    (Matrix.of fun i k => D k (f i)).det ≠ 0 ↔ Ideal.span (Set.range f) = maximalIdeal S := by sorry
