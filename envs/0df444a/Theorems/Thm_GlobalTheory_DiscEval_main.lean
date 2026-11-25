-- Prove2me | Theorems.Thm_GlobalTheory_DiscEval_main
-- name    : GlobalTheory.DiscEval.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:57:55.849352+00:00
-- url     : https://prove2.me/theorems/111a0f43-0a80-4210-a6c1-779f6f7319db
-- title:
--   Disc Eval: main
-- statement:
--   The Disc Eval construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L858-L919
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/BoundedOnFramesIffIntegralOnFrames.lean#L858-L919

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
open MvPolynomial

theorem GlobalTheory.DiscEval.main (p : ℕ) [Fact p.Prime] :
    (ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (algField p : Set ℂ_[p]) ∧
      (∀ t ∈ algDisc p, 0 < ‖t‖ ∧ ‖t‖ < 1) ∧
      (∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ algDisc p, |‖t‖ - r| < ε) ∧
      ∀ t ∈ algDisc p, ∀ τ ∈ algField p, ‖τ‖ = 1 → t * τ ∈ algDisc p) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] (i : O →+* ℂ_[p])
      (hi : ∀ x, ‖i x‖ ≤ 1) (_ : Function.Injective i) (π : O) (hπ : i π ≠ 0)
      (A : Type) [CommRing A] [Algebra O⟦X⟧ A]
      [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A],
      (∀ (t : ℂ_[p]) (ht0 : t ≠ 0) (ht : ‖t‖ < 1),
        (∀ f : O⟦X⟧,
          HasSum (fun n : ℕ => i (PowerSeries.coeff n f) * t ^ n) (discEval i hi ht f) ∧
          discEvalAway π A i hi hπ ht0 ht (algebraMap O⟦X⟧ A f) = discEval i hi ht f) ∧
        (∀ T : Set ℂ_[p], T.Finite → T ⊆ algField p → t ∈ T →
          (fieldEmb (genField i T)).fieldRange = Subfield.closure (Set.range i ∪ T) ∧
          ∃ (_ : FiniteDimensional ℚ_[p] (genField i T))
            (_ : IsDiscreteValuationRing (integralClosure ℤ_[p] (genField i T))),
            IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] (genField i T)))
              (integralClosure ℤ_[p] (genField i T)) ∧
            Finite (ResidueField (integralClosure ℤ_[p] (genField i T))) ∧
            IsFractionRing (integralClosure ℤ_[p] (genField i T)) (genField i T) ∧
            ∃ (ev : O⟦X⟧ →+* integralClosure ℤ_[p] (genField i T)) (evA : A →+* genField i T),
              (∀ f, intEmb _ (ev f) = discEval i hi ht f) ∧
              (∀ f, fieldEmb _ (evA f) = discEvalAway π A i hi hπ ht0 ht f) ∧
              evA.comp (algebraMap O⟦X⟧ A) = (algebraMap _ (genField i T)).comp ev ∧
              IsLocalHom ev ∧ (ev.comp PowerSeries.C).Finite ∧
              IsLocalHom (ev.comp PowerSeries.C)) ∧
        (∀ f : A,
          Tendsto (fun n : ℤ => ‖(laurent π A i hπ f).coeff n * t ^ n‖) cofinite (𝓝 0) ∧
          HasSum (fun n : ℤ => (laurent π A i hπ f).coeff n * t ^ n)
            (discEvalAway π A i hi hπ ht0 ht f)) ∧
        ∀ (f : A) (a b : ℕ) (f₀ : O⟦X⟧),
          f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀ →
          discEvalAway π A i hi hπ ht0 ht f = (i π)⁻¹ ^ a * t⁻¹ ^ b * discEval i hi ht f₀ ∧
          ∀ n : ℤ, (laurent π A i hπ f).coeff n =
            if n + b < 0 then 0 else (i π)⁻¹ ^ a * i (PowerSeries.coeff (n + b).natAbs f₀)) ∧
      ∀ (ι : Type) [Fintype ι] (n : ι → Type) [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
        (F : MvPolynomial (EntryIndex n n) A),
        (BoundedOnFrames i hi hπ F ↔ IntegralOnFrames i hi hπ F) ∧
        ∀ d : ℕ, F.IsHomogeneous d → BoundedOnFrames i hi hπ F →
          ∀ (B : EntryIndex n n → EntryIndex n n → ℂ_[p]) (c : ℝ), 1 ≤ c → (∀ k l, ‖B k l‖ ≤ c) →
            ∀ (μ : EntryIndex n n →₀ ℕ) (m : ℤ),
              ‖(coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
                (map (laurent π A i hπ) F))).coeff m‖ ≤ c ^ d ∧
              (m < 0 → (coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
                (map (laurent π A i hπ) F))).coeff m = 0) := by sorry
