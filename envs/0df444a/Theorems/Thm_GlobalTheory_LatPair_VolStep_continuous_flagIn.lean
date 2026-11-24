-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_VolStep_continuous_flagIn
-- name    : GlobalTheory.LatPair.VolStep.continuous_flagIn
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:58:59.8428+00:00
-- url     : https://prove2.me/theorems/3328d5eb-c68a-4f58-bb0a-5f86917a8616
-- title:
--   Vol Step: continuous flag In
-- statement:
--   The Vol Step construction uses the continuous flag In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlagVolumeOpenFiniteNonzero.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlagVolumeOpenFiniteNonzero.lean#L36-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlagVolumeOpenFiniteNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open scoped Pointwise ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.VolStep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [ValuativeRel k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.LatPair.VolStep.continuous_flagIn {n : Type} (c i : ℕ) : Continuous (flagIn (k := k) (n := n) c i) := by sorry
