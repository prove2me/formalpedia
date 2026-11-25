-- Prove2me | Theorems.Thm_GlobalTheory_MassOrth_mem_loc_span_iff
-- name    : GlobalTheory.MassOrth.mem_loc_span_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:22.079931+00:00
-- url     : https://prove2.me/theorems/03a61262-ae9e-4e24-b51c-7d9b3c9fbc32
-- title:
--   Mass Orth: mem loc span iff
-- statement:
--   The Mass Orth construction uses the mem loc span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L244-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L244-L276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MassOrth
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem GlobalTheory.MassOrth.mem_loc_span_iff {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (S : Set V) (x : V) :
    x ∈ loc (K := K) w.asIdeal (Submodule.span (𝓞 K) S) ↔
      x ∈ Submodule.span (biInt (w.valuation K)) S := by sorry
