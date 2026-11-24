-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_VolStep_isCompact_lat
-- name    : GlobalTheory.LatPair.VolStep.isCompact_lat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:00:07.844893+00:00
-- url     : https://prove2.me/theorems/33cb0e22-d2cf-49c2-9516-a35fde35334c
-- title:
--   Vol Step: is Compact lat
-- statement:
--   The Vol Step construction uses the is Compact lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlagVolumeOpenFiniteNonzero.lean#L13-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlagVolumeOpenFiniteNonzero.lean#L13-L33

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

theorem GlobalTheory.LatPair.VolStep.isCompact_lat {n : Type} [Fintype n] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    IsCompact (L : Set (n → k)) := by sorry
