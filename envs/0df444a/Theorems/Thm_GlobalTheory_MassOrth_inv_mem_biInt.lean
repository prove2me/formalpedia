-- Prove2me | Theorems.Thm_GlobalTheory_MassOrth_inv_mem_biInt
-- name    : GlobalTheory.MassOrth.inv_mem_biInt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:03.494689+00:00
-- url     : https://prove2.me/theorems/42ab80be-56bd-506c-b5eb-0974b3963196
-- title:
--   Mass Orth: inv mem bi Int
-- statement:
--   The Mass Orth construction uses the inv mem bi Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L211-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L211-L220

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

theorem GlobalTheory.MassOrth.inv_mem_biInt (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∈ hcompl (K := K) w.asIdeal) :
    algebraMap (𝓞 K) K s ≠ 0 ∧ (algebraMap (𝓞 K) K s)⁻¹ ∈ biInt (w.valuation K) := by sorry
