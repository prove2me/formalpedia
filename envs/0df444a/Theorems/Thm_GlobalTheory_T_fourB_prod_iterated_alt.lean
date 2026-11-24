-- Prove2me | Theorems.Thm_GlobalTheory_T_fourB_prod_iterated_alt
-- name    : GlobalTheory.T.fourB_prod_iterated_alt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:40:49.692377+00:00
-- url     : https://prove2.me/theorems/868f6d86-f600-41f2-9cd4-1c3c8391cb9a
-- title:
--   T: four B prod iterated alt
-- statement:
--   The T construction uses the four B prod iterated alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourBProdIteratedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourBProdIteratedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIterated
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIteratedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fourB_prod_iterated_alt : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂] [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂] (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm → ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ), Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) → (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) → ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y, fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := by sorry
