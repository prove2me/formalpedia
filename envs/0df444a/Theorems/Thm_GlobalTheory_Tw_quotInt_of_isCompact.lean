-- Prove2me | Theorems.Thm_GlobalTheory_Tw_quotInt_of_isCompact
-- name    : GlobalTheory.Tw.quotInt_of_isCompact
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:16.296881+00:00
-- url     : https://prove2.me/theorems/87b1563d-13bf-4c99-8b60-0e39e6388e17
-- title:
--   Tw: quot Int of is Compact
-- statement:
--   The Tw construction uses the quot Int of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L152-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L152-L161

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

theorem GlobalTheory.Tw.quotInt_of_isCompact (hT : IsCompact (T : Set G)) {F : G → ℂ} (hm : Measurable F)
    (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) : quotInt T μ μT F = ((μT.real Set.univ : ℝ) : ℂ)⁻¹ * ∫ x, F x ∂μ := by sorry
