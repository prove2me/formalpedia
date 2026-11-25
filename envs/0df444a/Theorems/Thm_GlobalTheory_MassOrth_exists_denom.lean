-- Prove2me | Theorems.Thm_GlobalTheory_MassOrth_exists_denom
-- name    : GlobalTheory.MassOrth.exists_denom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:19.847318+00:00
-- url     : https://prove2.me/theorems/cf25a63b-4470-4e84-8b6f-78a0e9573a46
-- title:
--   Mass Orth: exists denom
-- statement:
--   The Mass Orth construction uses the exists denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L222-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L222-L242

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

theorem GlobalTheory.MassOrth.exists_denom (w : HeightOneSpectrum (𝓞 K)) {k : K} (hk : k ∈ biInt (w.valuation K)) :
    ∃ s ∈ hcompl (K := K) w.asIdeal, ∃ a : 𝓞 K, algebraMap (𝓞 K) K s * k = algebraMap (𝓞 K) K a := by sorry
