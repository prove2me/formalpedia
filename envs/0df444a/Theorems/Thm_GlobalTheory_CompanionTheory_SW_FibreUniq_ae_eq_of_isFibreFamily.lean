-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreUniq_ae_eq_of_isFibreFamily
-- name    : GlobalTheory.CompanionTheory.SW.FibreUniq.ae_eq_of_isFibreFamily
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:29.881807+00:00
-- url     : https://prove2.me/theorems/c3603157-df6d-4e23-b3e3-b1082b9a3a2f
-- title:
--   Fibre Uniq: ae eq of is Fibre Family
-- statement:
--   The Fibre Uniq construction uses the ae eq of is Fibre Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityExists.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityExists.lean#L66-L76

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix Set
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreUniq

theorem GlobalTheory.CompanionTheory.SW.FibreUniq.ae_eq_of_isFibreFamily {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y}
    {g : V → X} {ι : X → Y} (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v))
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) (b : X) :
    ∀ᵐ v ∂(fib b), g v = b ∧ v ∈ U := by sorry
