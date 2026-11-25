-- Prove2me | Theorems.Thm_GlobalTheory_MassOrth_coe_starInt
-- name    : GlobalTheory.MassOrth.coe_starInt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:16:05.046505+00:00
-- url     : https://prove2.me/theorems/5c30dd1d-ff85-47de-88e0-f3488370da56
-- title:
--   Mass Orth: coe star Int
-- statement:
--   The Mass Orth construction uses the coe star Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L187-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L187-L187

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
omit [NumberField K]

theorem GlobalTheory.MassOrth.coe_starInt (s : 𝓞 K) : algebraMap (𝓞 K) K (starInt s) = star (algebraMap (𝓞 K) K s) := by sorry
