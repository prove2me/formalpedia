-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_QuotStep_exists_average
-- name    : GlobalTheory.RootEx.QuotStep.exists_average
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:08.005172+00:00
-- url     : https://prove2.me/theorems/02c2f1a0-cae9-47a2-963d-2c0814cda382
-- title:
--   Quot Step: exists average
-- statement:
--   The Quot Step construction uses the exists average property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/WeilFormulaRootExchangeParabolicIntersection.lean#L35-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/WeilFormulaRootExchangeParabolicIntersection.lean#L35-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotStep

theorem GlobalTheory.RootEx.QuotStep.exists_average {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [TopologicalSpace X] [TopologicalSpace U] [MeasurableSpace X] [MeasurableSpace U]
    [OpensMeasurableSpace (X × U)] [T2Space X] [T2Space U]
    (μ : Measure X) (ρ : Measure U) [SFinite μ] [SFinite ρ] [IsFiniteMeasureOnCompacts (μ.prod ρ)]
    [(μ.prod ρ).IsOpenPosMeasure]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (ι : X × U → G) (hι : Continuous ι) (t₁ : X × U) (h₁ : ι t₁ = 1)
    (hprop : ∀ C : Set G, IsCompact C → ∃ D, IsCompact D ∧ ∀ t, ι t ∈ C → t ∈ D)
    (δ : X → ℝ) (hδ : Continuous δ) (hδ0 : ∀ x, 0 < δ x)
    (hinv : ∀ φ : G → ℂ, Continuous φ → ∀ t, ∫ x, ∫ u, (δ x : ℂ) * φ (ι (x, u) * ι t) ∂ρ ∂μ =
      ∫ x, ∫ u, (δ x : ℂ) * φ (ι (x, u)) ∂ρ ∂μ)
    (f : G → ℂ) (hf : IsLocallyConstant f) (Ω : Set G) (hΩ : IsCompact Ω)
    (hsupp : ∀ h, f h ≠ 0 → ∃ t, ∃ w ∈ Ω, h = ι t * w)
    (hfδ : ∀ t h, f (ι t * h) = δ t.1 * f h) :
    ∃ F ∈ SB G, ∀ h, f h = ∫ x, ∫ u, F (ι (x, u) * h) ∂ρ ∂μ := by sorry
