-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatDet_mem_locR_iff_le
-- name    : GlobalTheory.MaxLatDet.mem_locR_iff_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:10:11.52506+00:00
-- url     : https://prove2.me/theorems/8f300bcb-638d-4b0d-9a1c-c3597bff18c0
-- title:
--   Max Lat Det: mem loc R iff le
-- statement:
--   The Max Lat Det construction uses the mem loc R iff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeBadPrimesIffGramDet.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeBadPrimesIffGramDet.lean#L56-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDet
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
open GlobalTheory GlobalTheory.MaxLatDet
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem GlobalTheory.MaxLatDet.mem_locR_iff_le (w : HeightOneSpectrum (𝓞 K)) (hw : conjIdeal (K := K) w.asIdeal = w.asIdeal)
    (k : K) : k ∈ locR (K := K) w.asIdeal ↔ w.valuation K k ≤ 1 := by sorry
