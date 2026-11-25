-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatDet_det_gram
-- name    : GlobalTheory.MaxLatDet.det_gram
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:10:29.438989+00:00
-- url     : https://prove2.me/theorems/2f2869f0-a8e5-4633-a5b5-48fce5294aa9
-- title:
--   Max Lat Det: det gram
-- statement:
--   The Max Lat Det construction uses the det gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeBadPrimesIffGramDet.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeBadPrimesIffGramDet.lean#L33-L48

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
variable {K V ι : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]

theorem GlobalTheory.MaxLatDet.det_gram [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K) (e b : Module.Basis ι K V)
    (he : ∀ i l, i ≠ l → h (e i) (e l) = 0) :
    ∃ δ : K, δ ≠ 0 ∧ (Matrix.of fun i l => h (b i) (b l)).det = star δ * δ * ∏ i, h (e i) (e i) := by sorry
