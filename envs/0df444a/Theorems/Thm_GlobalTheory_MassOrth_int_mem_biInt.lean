-- Prove2me | Theorems.Thm_GlobalTheory_MassOrth_int_mem_biInt
-- name    : GlobalTheory.MassOrth.int_mem_biInt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:35.137525+00:00
-- url     : https://prove2.me/theorems/84cdfccf-92a3-4d27-9f7e-83cb1ed8a364
-- title:
--   Mass Orth: int mem bi Int
-- statement:
--   The Mass Orth construction uses the int mem bi Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L207-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L207-L209

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

theorem GlobalTheory.MassOrth.int_mem_biInt (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    algebraMap (𝓞 K) K a ∈ biInt (w.valuation K) := by sorry
