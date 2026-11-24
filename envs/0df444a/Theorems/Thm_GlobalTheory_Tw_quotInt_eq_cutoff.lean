-- Prove2me | Theorems.Thm_GlobalTheory_Tw_quotInt_eq_cutoff
-- name    : GlobalTheory.Tw.quotInt_eq_cutoff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:22.979107+00:00
-- url     : https://prove2.me/theorems/f2bbc6ce-44bb-4851-aeba-36a08df753b0
-- title:
--   Tw: quot Int eq cutoff
-- statement:
--   The Tw construction uses the quot Int eq cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L137-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L137-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {T : Subgroup G} {μ : Measure G} {μT : Measure T}
variable [LocallyCompactSpace G] [T2Space G] [SFinite μ] [μ.IsMulLeftInvariant] [μT.IsHaarMeasure] [μT.IsInvInvariant]

theorem GlobalTheory.Tw.quotInt_eq_cutoff (hT : IsClosed (T : Set G)) {β : G → NNReal} (hβ : IsCosetCutoff T μT β) {F : G → ℂ}
    (hm : Measurable F) (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) : quotInt T μ μT F = ∫ x, (β x : ℝ) • F x ∂μ := by sorry
