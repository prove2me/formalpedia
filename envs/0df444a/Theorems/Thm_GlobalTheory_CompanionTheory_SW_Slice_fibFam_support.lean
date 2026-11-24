-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_fibFam_support
-- name    : GlobalTheory.CompanionTheory.SW.Slice.fibFam_support
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:37.465823+00:00
-- url     : https://prove2.me/theorems/d9d51ffa-9975-48e2-a855-78450612c65d
-- title:
--   Slice: fib Fam support
-- statement:
--   The Slice construction uses the fib Fam support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L167-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L167-L198

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

theorem GlobalTheory.CompanionTheory.SW.Slice.fibFam_support {Y : Type} {f : V → Y} {g : V → X} {ι : X → Y} (hι : Function.Injective ι)
    (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) (w : Q → ℝ≥0) (m : Measure (g ⁻¹' {b₀}))
    (b : X) :
    fibFam g b₀ w m b (f ⁻¹' {ι b} ∩ g ⁻¹' Set.range (fun q : Q => q • b₀))ᶜ = 0 := by sorry
