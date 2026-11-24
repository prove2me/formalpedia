-- Prove2me | Theorems.Thm_GlobalTheory_HeisUnit_orth_of_charsep
-- name    : GlobalTheory.HeisUnit.orth_of_charsep
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:17:46.706729+00:00
-- url     : https://prove2.me/theorems/97f36fb2-6778-4032-8deb-ee90de176fb9
-- title:
--   Heis Unit: orth of charsep
-- statement:
--   The Heis Unit construction uses the orth of charsep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeisenbergCosetRepTranslatesOrthogonal.lean#L79-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeisenbergCosetRepTranslatesOrthogonal.lean#L79-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryAndSeparates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergCosetRepTranslatesOrthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.HeisUnit

theorem GlobalTheory.HeisUnit.orth_of_charsep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ)
    (hcs : (∀ x, ‖ψ0 x‖ = 1) ∧ ∀ a : k, a ∉ 𝒪[k] → ∃ c : k, (∀ y ∈ 𝒪[k], ψ0 (c * y) = 1) ∧ ψ0 (c * a) ≠ 1)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd k n d)
    (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res k 1) (hTT : T ≠ T')
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫ y, Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) ∂μ = 0 := by sorry
