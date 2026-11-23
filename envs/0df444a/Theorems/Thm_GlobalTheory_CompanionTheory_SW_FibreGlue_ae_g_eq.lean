-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreGlue_ae_g_eq
-- name    : GlobalTheory.CompanionTheory.SW.FibreGlue.ae_g_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:24.207659+00:00
-- url     : https://prove2.me/theorems/0d3af5da-1c15-447d-a5e1-6c9fc6d0b118
-- title:
--   Fibre Glue: ae g eq
-- statement:
--   The Fibre Glue construction uses the ae g eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RestrFamily.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RestrFamily.lean#L18-L25

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExistsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RestrFamily
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreGlue
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y}

theorem GlobalTheory.CompanionTheory.SW.FibreGlue.ae_g_eq (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v)) {U : Set V} {m : Measure V}
    {b : X} (h : m (f ⁻¹' {ι b} ∩ U)ᶜ = 0) : ∀ᵐ v ∂m, g v = b := by sorry
