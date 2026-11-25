-- Prove2me | Theorems.Thm_GlobalTheory_Mass_LocWitt_star_int
-- name    : GlobalTheory.Mass.LocWitt.star_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:01:40.2578+00:00
-- url     : https://prove2.me/theorems/e55b79cb-e0c4-5f14-93fc-65efc60d22d6
-- title:
--   Loc Witt: star int
-- statement:
--   The Loc Witt construction uses the star int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemHcompl.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemHcompl.lean#L166-L168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LocWitt

theorem GlobalTheory.Mass.LocWitt.star_int {K : Type} [Field K] [NumberField K] [StarRing K] (r : 𝓞 K) :
    ∃ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K r) := by sorry
