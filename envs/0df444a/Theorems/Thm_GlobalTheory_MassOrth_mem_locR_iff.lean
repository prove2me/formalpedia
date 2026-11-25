-- Prove2me | Theorems.Thm_GlobalTheory_MassOrth_mem_locR_iff
-- name    : GlobalTheory.MassOrth.mem_locR_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:39.805184+00:00
-- url     : https://prove2.me/theorems/00de2d6c-845a-4e8e-9917-7f25b7c7c8d5
-- title:
--   Mass Orth: mem loc R iff
-- statement:
--   The Mass Orth construction uses the mem loc R iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L278-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L278-L285

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

theorem GlobalTheory.MassOrth.mem_locR_iff (w : HeightOneSpectrum (𝓞 K)) (k : K) :
    k ∈ locR (K := K) w.asIdeal ↔ k ∈ biInt (w.valuation K) := by sorry
