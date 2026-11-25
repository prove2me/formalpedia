-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfDualUnramifiedPlaces_mem_maxOrder
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.mem_maxOrder
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:10:59.743314+00:00
-- url     : https://prove2.me/theorems/e5c663b8-09e4-40f0-ac26-617dee00b6a5
-- title:
--   Self Dual Unramified Places: mem max Order
-- statement:
--   The Self Dual Unramified Places construction uses the mem max Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/SelfDualUnramifiedPlaces.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/SelfDualUnramifiedPlaces.lean#L36-L40

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.mem_maxOrder (v : HeightOneSpectrum (𝓞 F))
    (z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v ↔
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.intToEv F E v).IsIntegralElem z := by sorry
