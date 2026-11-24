-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_lintegral_fibFam
-- name    : GlobalTheory.CompanionTheory.SW.Slice.lintegral_fibFam
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:09.858859+00:00
-- url     : https://prove2.me/theorems/0a5fbb54-a40d-4266-9a82-961e0c433e75
-- title:
--   Slice: lintegral fib Fam
-- statement:
--   The Slice construction uses the lintegral fib Fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L332-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L332-L399

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Slice
variable {V X Q : Type} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
  [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
  [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]

theorem GlobalTheory.CompanionTheory.SW.Slice.lintegral_fibFam [T2Space V] {g : V → X} (hg : Continuous g)
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) (μ : Measure V) (ν : Measure X)
    (χ χ' : Q →* ℝ≥0) (hχ : Continuous χ) (hχ' : Continuous χ')
    (m : Measure (g ⁻¹' {b₀})) [SFinite m]
    [SFinite ((ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞)))]
    (hm : (μ.comap (theta (Q := Q) g b₀)).withDensity (fun p => (χ p.1 : ℝ≥0∞)) =
        ((ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞))).prod m)
    {φ : V → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ v in g ⁻¹' Set.range (fun q : Q => q • b₀), φ v ∂μ =
      ∫⁻ b, ∫⁻ v, φ v ∂(fibFam g b₀ (fun q => χ' q * χ q⁻¹) m b) ∂ν := by sorry
