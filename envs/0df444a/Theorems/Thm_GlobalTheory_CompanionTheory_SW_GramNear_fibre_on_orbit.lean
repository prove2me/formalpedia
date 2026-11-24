-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramNear_fibre_on_orbit
-- name    : GlobalTheory.CompanionTheory.SW.GramNear.fibre_on_orbit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:19.617659+00:00
-- url     : https://prove2.me/theorems/c3d3eb57-c4be-41d6-9170-06de1c0a47e3
-- title:
--   Gram Near: fibre on orbit
-- statement:
--   The Gram Near construction uses the fibre on orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasureDisintegrationFormula.lean#L16-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasureDisintegrationFormula.lean#L16-L32

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroupStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousActionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureDisintegrationFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramNear

theorem GlobalTheory.CompanionTheory.SW.GramNear.fibre_on_orbit (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V]
    [AddCommGroup X] [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [IsTopologicalAddGroup X]
    (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v))
    (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [DistribMulAction Q V] [ContinuousSMul Q V]
    [DistribMulAction Q X] [ContinuousSMul Q X]
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) (b₀ : X)
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) :
    ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' (Set.range fun q : Q => q • b₀)) ν
      (Set.range fun q : Q => q • b₀) fib := by sorry
