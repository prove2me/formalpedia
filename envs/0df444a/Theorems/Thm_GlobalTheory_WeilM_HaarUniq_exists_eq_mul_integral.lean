-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_eq_mul_integral
-- name    : GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:52.477092+00:00
-- url     : https://prove2.me/theorems/57ed7a37-04c4-4663-ba6f-40d607663e80
-- title:
--   Haar Uniq: exists eq mul integral
-- statement:
--   The Haar Uniq construction uses the exists eq mul integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenAddSubgroup.lean#L152-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenAddSubgroup.lean#L152-L199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.WeilM GlobalTheory.WeilM.HaarUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
open MeasureTheory Filter Topology
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

theorem GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral : ∀ (V : Type) [AddCommGroup V]
    [TopologicalSpace V] [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure]
    (m : (V → ℂ) →ₗ[ℂ] ℂ), (∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, ∀ a : V,
      m (fun x => φ (x + a)) = m φ) →
    ∃ c : ℂ, ∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, m φ = c * ∫ x, φ x ∂μ := by sorry
