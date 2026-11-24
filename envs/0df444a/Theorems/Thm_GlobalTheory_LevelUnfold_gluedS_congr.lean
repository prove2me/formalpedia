-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnfold_gluedS_congr
-- name    : GlobalTheory.LevelUnfold.gluedS_congr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:22.032687+00:00
-- url     : https://prove2.me/theorems/88156279-9901-488a-8ab2-fc407028a9cd
-- title:
--   Level Unfold: glued S congr
-- statement:
--   The Level Unfold construction uses the glued S congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L116-L119

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

theorem GlobalTheory.LevelUnfold.gluedS_congr {L : Submodule 𝒪[k] (n → k)} {f f' : n → k}
    (h : f - f' ∈ L) : _root_.GlobalTheory.LatPair.gluedS q c L f = _root_.GlobalTheory.LatPair.gluedS q c L f' := by sorry
