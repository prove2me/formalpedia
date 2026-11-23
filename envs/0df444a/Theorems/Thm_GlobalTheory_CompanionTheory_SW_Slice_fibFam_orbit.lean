-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_fibFam_orbit
-- name    : GlobalTheory.CompanionTheory.SW.Slice.fibFam_orbit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:19.565799+00:00
-- url     : https://prove2.me/theorems/05b3edbd-b96d-4657-b260-d92a860f2f72
-- title:
--   Slice: fib Fam orbit
-- statement:
--   The Slice construction uses the fib Fam orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L152-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L152-L157

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

theorem GlobalTheory.CompanionTheory.SW.Slice.fibFam_orbit {g : V → X} {b₀ : X} (w : Q → ℝ≥0) (m : Measure (g ⁻¹' {b₀}))
    (ho : Function.Injective (fun q : Q => q • b₀)) (q : Q) :
    fibFam g b₀ w m (q • b₀) = (w q : ℝ≥0∞) • m.map (fun z : (g ⁻¹' {b₀}) => q • (z : V)) := by sorry
