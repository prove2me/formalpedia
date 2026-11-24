-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreGlue_restr_family
-- name    : GlobalTheory.CompanionTheory.SW.FibreGlue.restr_family
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:04:32.151808+00:00
-- url     : https://prove2.me/theorems/491d9e30-f86e-4c73-a6fc-665a50055d2d
-- title:
--   Fibre Glue: restr family
-- statement:
--   The Fibre Glue construction uses the restr family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RestrFamily.lean#L58-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RestrFamily.lean#L58-L89

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

theorem GlobalTheory.CompanionTheory.SW.FibreGlue.restr_family (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {B B₂ : Set X} (hB₂ : IsOpen B₂) (hsub : B₂ ⊆ B) {fam : X → Measure V}
    (h : IsFibreFamily μ f ι (g ⁻¹' B) ν B fam) :
    IsFibreFamily μ f ι (g ⁻¹' B₂) ν B₂ (restr B₂ fam) := by sorry
