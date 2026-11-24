-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfDualUnramifiedPlaces_density_factor_pos
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.density_factor_pos
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:30.151013+00:00
-- url     : https://prove2.me/theorems/e65c1560-7b2a-4ad6-ab87-4daee555db3e
-- title:
--   Self Dual Unramified Places: density factor pos
-- statement:
--   The Self Dual Unramified Places construction uses the density factor pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/SelfDualUnramifiedPlaces.lean#L108-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/SelfDualUnramifiedPlaces.lean#L108-L122

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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

theorem GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.density_factor_pos (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (M : ℕ) (hM : 1 ≤ M) :
    0 < 1 - _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M *
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹ := by sorry
