-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnfold_interX_gluedS
-- name    : GlobalTheory.LevelUnfold.interX_gluedS
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:35.736062+00:00
-- url     : https://prove2.me/theorems/e0a69826-8e80-5f46-a9c5-0bf06f404c44
-- title:
--   Level Unfold: inter X glued S
-- statement:
--   The Level Unfold construction uses the inter X glued S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L68-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSmulOfMemFlagSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : Unif k}
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k}

theorem GlobalTheory.LevelUnfold.interX_gluedS (hc : 1 ≤ c) (L : Submodule 𝒪[k] (n → k))
    (f : n → k) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration.interX (_root_.GlobalTheory.LatPair.gluedS q c L f) = L := by sorry
