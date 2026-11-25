-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatDet_val_star
-- name    : GlobalTheory.MaxLatDet.val_star
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:10:38.46686+00:00
-- url     : https://prove2.me/theorems/342f5006-a7f8-4d97-b35a-7e7df82c2d8d
-- title:
--   Max Lat Det: val star
-- statement:
--   The Max Lat Det construction uses the val star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeBadPrimesIffGramDet.lean#L64-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeBadPrimesIffGramDet.lean#L64-L81

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

theorem GlobalTheory.MaxLatDet.val_star (w : HeightOneSpectrum (𝓞 K)) (hw : conjIdeal (K := K) w.asIdeal = w.asIdeal)
    (k : K) : w.valuation K (star k) = w.valuation K k := by sorry
